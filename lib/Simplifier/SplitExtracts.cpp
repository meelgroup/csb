/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: May-2022
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Simplifier/SubstitutionMap.h"

namespace stp
{
  void SplitExtracts::buildMap(const ASTNode & n, std::unordered_set<uint64_t> &visited, NodeToExtractsMap& nodeToExtracts)
  {
    if (n.Degree() == 0)
      return;

    if (!visited.insert(n.GetNodeNum()).second)
      return;

    for (const auto & c :n)
    {
      if (c.GetKind() == stp::SYMBOL && n.GetKind() == stp::BVEXTRACT)
      {
        nodeToExtracts[c].push_back(std::make_tuple(n, n[1].GetUnsignedConst(), n[2].GetUnsignedConst()));
        extractsFound++;
      }
      else if (c.GetKind() == stp::SYMBOL)
      {
      nodeToExtracts[c].push_back(std::make_tuple(ASTUndefined, UINT64_MAX,0));
      }

      buildMap(c,visited,nodeToExtracts);
    }
  }

  ASTNode SplitExtracts::topLevel(const ASTNode& n)
  { 
    assert(bm.UserFlags.enable_split_extracts);

    // TODO doesn't construct the model yet.
    // It requires a messy implementation.
    if (bm.UserFlags.construct_counterexample_flag)
    {
      if (bm.UserFlags.stats_flag)
        std::cerr << "{Split Extracts} Disabled" << std::endl;
      return n;
    }

    ASTNode result = n;

    introduced = 0;
    extractsFound =0;

    // Needs the full global context to figure it out.
    // Think, we might be able to keep visited between invocations
    // of topLevel if no extracts are found?
    NodeToExtractsMap  nodeToExtracts;

    bm.GetRunTimes()->start(RunTimes::SplitExtracts);

    std::unordered_set<uint64_t> visited;
    buildMap(n,visited, nodeToExtracts);

    if (extractsFound > 0)
    {
      ASTNodeMap fromTo;
      // For each symbol whose every (non-extract) reference is via an extract
      // that we are about to replace, we additionally need to record a
      // substitution `symbol -> concat(fresh_pieces + padding)` so that the
      // model count multiplier is computed correctly. Without it the
      // declared symbol disappears from the formula AND from the
      // substitution map, so the count code would credit it with its full
      // 2^w degrees of freedom even though only the unextracted "gap" bits
      // are actually unconstrained.
      using PieceRange = std::tuple<ASTNode, uint64_t, uint64_t>;
      std::unordered_map<ASTNode, std::vector<PieceRange>,
                         ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
          fully_replaced_symbol_pieces;

      for (const auto& e: nodeToExtracts )
      {
        const auto& symbol = e.first;
        assert(symbol.GetKind() == SYMBOL);

        auto ranges = e.second;

        if (ranges.size() < 2)
          continue; // Don't want to split if there's just one.

        auto comp = [](const auto& p0, const auto& p1)
        {
          return std::get<2>(p0) < std::get<2>(p1);
        };

        // Afterwards e.g. (4,0) (3,3) (8,5)
        sort(ranges.begin(), ranges.end(), comp);

        uint64_t highest = 0;

        // Was every recorded use of `symbol` an extract that we replaced?
        // Any bare-symbol-use sentinel (high == UINT64_MAX) means the
        // symbol survives in the formula and the simplification of any of
        // its extracts in isolation would be unsound (the fresh
        // replacement is no longer linked to the symbol's bits). The
        // original code relied on a UINT64_MAX `highest` to disable
        // replace; we preserve that and additionally track fully_covered
        // for the substitution-map bookkeeping further down.
        bool fully_covered = true;
        std::vector<PieceRange> pieces; // (fresh, high, low)

        for (unsigned i = 0; i < ranges.size(); i++)
        {
          const auto extract = std::get<0>(ranges[i]);
          const auto high = std::get<1>(ranges[i]);
          const auto low = std::get<2>(ranges[i]);
          assert(high >= low);
          const bool bare_use = (high == UINT64_MAX);

          bool replace = !bare_use;
          if (i+1 != ranges.size())  // check up.
          {
            // e.g. if (4,3) (6,4)..
            if (std::get<2>(ranges[i+1]) <= high)
            replace = false;
          }

        if (i != 0) // check down.
        {
            if (low <= highest)
            replace = false;

          highest = std::max(high, highest);
        }
        else
        {
          highest = high;
        }

          if (replace)
          {
          assert(extract.GetKind() == BVEXTRACT);
          assert(extract[0] == symbol);
            const auto fresh = bm.CreateFreshVariable(0,high-low+1, "_STP");
          fromTo.insert({extract,fresh});
          introduced++;
          pieces.emplace_back(fresh, high, low);
          }
          else if (!bare_use)
          {
            fully_covered = false; // overlapping/unhandled extract stays
          }
          else
          {
            fully_covered = false; // bare-symbol use keeps the symbol live
          }
        }

        if (fully_covered && !pieces.empty())
          fully_replaced_symbol_pieces[symbol] = std::move(pieces);
      }

      if (fromTo.size() > 0)
      {
        ASTNodeMap cache;
        result = stp::SubstitutionMap::replace(n, fromTo, cache, bm.defaultNodeFactory);
      }

      // After replacing the extracts, install a `symbol -> concat(...)`
      // substitution for each symbol whose every use was a replaced extract
      // -- this is what tells the unconstrained-bit recompute that the
      // symbol's bits are already tracked through the fresh pieces, while
      // the gap (unextracted) bits remain to be counted as a multiplier.
      if (simp != nullptr)
      {
        for (auto& kv : fully_replaced_symbol_pieces)
        {
          const ASTNode& symbol = kv.first;
          if (simp->Return_SolverMap()->find(symbol) !=
              simp->Return_SolverMap()->end())
            continue; // already substituted by another pass

          auto& pieces = kv.second;
          // pieces are extracts of `symbol`. Sort low-to-high.
          std::sort(pieces.begin(), pieces.end(),
                    [](const PieceRange& a, const PieceRange& b) {
                      return std::get<2>(a) < std::get<2>(b);
                    });

          const uint64_t total_w = symbol.GetValueWidth();
          ASTVec concat_pieces; // index 0 = most-significant
          uint64_t cursor = 0;
          for (const auto& p : pieces)
          {
            const ASTNode& fresh = std::get<0>(p);
            const uint64_t high = std::get<1>(p);
            const uint64_t low = std::get<2>(p);
            if (low > cursor)
            {
              const uint64_t pad_w = low - cursor;
              ASTNode pad =
                  bm.CreateFreshVariable(0, pad_w, "_STP_split_pad");
              // concat is most-significant-first, but we accumulate
              // little-endian and reverse at the end.
              concat_pieces.push_back(pad);
            }
            concat_pieces.push_back(fresh);
            cursor = high + 1;
          }
          if (cursor < total_w)
          {
            const uint64_t pad_w = total_w - cursor;
            ASTNode pad =
                bm.CreateFreshVariable(0, pad_w, "_STP_split_pad");
            concat_pieces.push_back(pad);
          }

          if (concat_pieces.size() == 1)
          {
            simp->UpdateSolverMap(symbol, concat_pieces[0]);
          }
          else
          {
            // Reverse so the highest-bit piece comes first (BVCONCAT
            // convention: first child is most significant).
            std::reverse(concat_pieces.begin(), concat_pieces.end());
            ASTNode current = concat_pieces[0];
            for (size_t i = 1; i < concat_pieces.size(); i++)
            {
              const uint64_t new_w = current.GetValueWidth()
                                     + concat_pieces[i].GetValueWidth();
              current = bm.defaultNodeFactory->CreateTerm(
                  BVCONCAT, new_w, current, concat_pieces[i]);
            }
            simp->UpdateSolverMap(symbol, current);
          }
        }
      }
    }

    bm.GetRunTimes()->stop(RunTimes::SplitExtracts);

    if (bm.UserFlags.stats_flag)
    {
      std::cerr << "{Split Extracts} Extracts over variables found: " << extractsFound << std::endl;
      std::cerr << "{Split Extracts} variables introduced: " << introduced << std::endl;
    }

    return result;
  }
}
