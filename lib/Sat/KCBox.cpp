/********************************************************************
 * AUTHORS: OpenAI Assistant
 *
 * BEGIN DATE: February, 2025
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ********************************************************************/

#include "stp/Sat/KCBox.h"

#include "Counters/KCounter.h"
#include "Counters/WCounter.h"
#include "KC_Languages/OBDD[AND].h"
#include "Compilers/BDDC_Compiler.h"
#include "Primitive_Types/CNF_Formula.h"
#include "Template_Library/Basic_Structures.h"

#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <cmath>
#include <streambuf>

namespace stp
{

using namespace KCBox;

namespace
{
class StreamSilencer
{
public:
  explicit StreamSilencer(int verbosity)
  {
    if (verbosity <= 0)
    {
      cout_buf = std::cout.rdbuf(&null_buffer);
      cerr_buf = std::cerr.rdbuf(&null_buffer);
      silenced = true;
    }
  }

  ~StreamSilencer() { restore(); }

  void restore()
  {
    if (silenced)
    {
      std::cout.rdbuf(cout_buf);
      std::cerr.rdbuf(cerr_buf);
      silenced = false;
    }
  }

private:
  class NullBuffer : public std::streambuf
  {
  protected:
    int overflow(int c) override { return c; }
  };

  NullBuffer null_buffer;
  std::streambuf* cout_buf = nullptr;
  std::streambuf* cerr_buf = nullptr;
  bool silenced = false;
};
} // namespace

KCBox::KCBox(uint64_t sampler_seed, bool enable_sampling, bool enable_counting)
    : seed(sampler_seed), max_var(0), sampling_enabled(enable_sampling),
      counting_enabled(enable_counting)
{
  if (verbosity > 0)
    std::cout << "c [stp->KCBox] KCBox initialized" << std::endl;
}

KCBox::~KCBox() = default;

void KCBox::ensureWeightSize(size_t var_index)
{
  if (weights.size() <= var_index)
  {
    weights.resize(var_index + 1, 1.0);
    neg_weights.resize(var_index + 1, 1.0);
  }
}

bool KCBox::addClause(const vec_literals& ps)
{
  std::vector<int> clause;
  clause.reserve(ps.size());
  for (int i = 0; i < ps.size(); ++i)
  {
    const bool is_neg = sign(ps[i]);
    const uint32_t var_id = var(ps[i]);
    const uint32_t ext = var_id + 1;
    clause.push_back(is_neg ? -ext : ext);
    if (ext > max_var)
      max_var = ext;
  }
  clauses.push_back(std::move(clause));
  return true;
}

bool KCBox::okay() const
{
  return true;
}

bool KCBox::solve(bool& timeout_expired)
{
  timeout_expired = false;
  sample_available = false;
  sampled_assignment.clear();
  StreamSilencer silence(verbosity);

  // Compact variable numbering to avoid gaps that introduce spurious free
  // variables in the counting backend.
  uint32_t next_var = 1;
  std::vector<uint32_t> remap(max_var + 1, 0);
  for (const auto& clause : clauses)
  {
    for (int lit : clause)
    {
      const uint32_t v = static_cast<uint32_t>(std::abs(lit));
      if (remap[v] == 0)
      {
        remap[v] = next_var++;
      }
    }
  }

  if (next_var - 1 != max_var)
  {
    for (auto& clause : clauses)
    {
      for (int& lit : clause)
      {
        const bool is_neg = lit < 0;
        const uint32_t old_var = static_cast<uint32_t>(std::abs(lit));
        const uint32_t new_var = remap[old_var];
        lit = is_neg ? -static_cast<int>(new_var) : static_cast<int>(new_var);
      }
    }

    std::vector<double> new_weights(next_var - 1, 1.0);
    std::vector<double> new_neg_weights(next_var - 1, 1.0);
    for (uint32_t old_var = 1; old_var < remap.size(); ++old_var)
    {
      const uint32_t new_var = remap[old_var];
      if (new_var == 0)
        continue;
      const uint32_t old_idx = old_var - 1;
      const uint32_t new_idx = new_var - 1;
      if (old_idx < weights.size())
        new_weights[new_idx] = weights[old_idx];
      if (old_idx < neg_weights.size())
        new_neg_weights[new_idx] = neg_weights[old_idx];
    }
    weights.swap(new_weights);
    neg_weights.swap(new_neg_weights);
    max_var = next_var - 1;
  }

  const bool has_weights = weights_specified;
  CNF_Formula cnf(clauses);

  // Guard against stray solver variables by syncing to the actual maximum
  // variable referenced in the CNF produced by ABC.
  max_var = static_cast<uint32_t>(cnf.Max_Var());

  if (counting_enabled)
  {
    if (has_weights)
    {
      WCNF_Formula wcnf(cnf);
      for (uint32_t var = 0; var < max_var; ++var)
      {
        const double pos_weight = (var < weights.size()) ? weights[var] : 1.0;
        const double neg_weight =
            (var < neg_weights.size()) ? neg_weights[var] : 1.0;

        wcnf.Set_Weight(InternLit(static_cast<int>(var + 1)), pos_weight);
        wcnf.Set_Weight(~InternLit(static_cast<int>(var + 1)), neg_weight);
      }

      if (verbosity > 0)
      {
        std::cout << "c [stp->KCBox] Arjun solving instance with " << max_var
                  << " variables, " << clauses.size() << " clauses"
                  << std::endl;
      }

      WCounter counter;
      auto estimate = counter.Count_Models(wcnf);
      const long double log10_estimate = estimate.Log10();
      silence.restore();
      std::cout << "c s log10-estimate " << std::scientific
                << std::setprecision(8) << static_cast<double>(log10_estimate)
                << std::endl;
      std::cout << "c o exact quadruple float " << std::scientific
                << std::setprecision(8) << estimate.TransformDouble()
                << std::endl;
    }
    else
    {
      KCounter counter;
      auto total = counter.Count_Models(cnf);
      long exp = 0;
      const double base = total.TransformDouble_2exp(exp);
      const long double log10_estimate =
          std::log10(static_cast<long double>(base)) +
          static_cast<long double>(exp) * std::log10(2.0L);
      silence.restore();
      std::cout << "c s log10-estimate " << std::scientific
                << std::setprecision(8) << static_cast<double>(log10_estimate)
                << std::endl;
      std::cout << "c o exact quadruple float " << std::scientific
                << std::setprecision(8) << total.TransformDouble() << std::endl;
    }
  }

  if (sampling_enabled)
  {
    BDDC_Compiler compiler;
    Smooth_OBDDC_Manager manager(cnf.Max_Var());
    auto diagram = compiler.Compile(manager, cnf, AutomaticalHeur);
    Random_Generator rng;
    rng.Reset(seed);
    std::vector<std::vector<bool>> samples(1);
    manager.Uniformly_Sample(rng, diagram, samples);
    if (!samples.empty())
    {
      const auto& first_sample = samples.front();
      sampled_assignment.resize(first_sample.size(), 0);
      for (size_t i = 0; i < first_sample.size(); ++i)
      {
        sampled_assignment[i] = first_sample[i] ? static_cast<int8_t>(1)
                                                : static_cast<int8_t>(-1);
      }
      sample_available = true;
    }
  }

  if (counting_enabled && !sampling_enabled)
  {
    std::cout.flush();
    std::cerr.flush();
    std::_Exit(0);
  }

  return true;
}

uint8_t KCBox::modelValue(uint32_t x) const
{
  if (!sample_available)
    return static_cast<uint8_t>(0);

  if (sampled_assignment.empty())
    return static_cast<uint8_t>(0);

  if (x >= sampled_assignment.size())
    return static_cast<uint8_t>(0);

  return static_cast<uint8_t>(sampled_assignment[x]);
}

uint32_t KCBox::newProjVar(uint32_t x)
{
  projected_vars.push_back(x + 1);
  return 1;
}

uint32_t KCBox::newVar()
{
  const uint32_t next = max_var;
  max_var = next + 1;
  ensureWeightSize(next);
  return next;
}

void KCBox::setVarWeight(uint32_t var, double weight)
{
  ensureWeightSize(var);
  weights[var] = weight;
  weights_specified = weights_specified || weight != 1.0;
}

void KCBox::setNegWeight(uint32_t var, double weight)
{
  ensureWeightSize(var);
  neg_weights[var] = weight;
  weights_specified = weights_specified || weight != 1.0;
}

void KCBox::setVerbosity(int v)
{
  verbosity = v;
}

unsigned long KCBox::nVars() const
{
  return max_var;
}

void KCBox::printStats() const
{
  if (verbosity > 0)
  {
    std::cout << "c kcbox clauses " << clauses.size() << " vars " << max_var + 1
              << std::endl;
  }
}

} // namespace stp
