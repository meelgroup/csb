#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Sat/SimplifyingMinisat.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ToSATAIG.h"

#include <gtest/gtest.h>

#include <cassert>
#include <functional>
#include <initializer_list>
#include <utility>
#include <vector>

namespace
{

using ManualBuilder = std::function<void(stp::SATSolver& solver,
                                         const std::vector<unsigned>& lhs,
                                         const std::vector<unsigned>& rhs,
                                         std::vector<unsigned>& out)>;

void addClauseOrFail(stp::SATSolver& solver,
                     std::initializer_list<Minisat::Lit> literals)
{
  stp::SATSolver::vec_literals clause;
  for (const auto& lit : literals)
    clause.push(lit);
  ASSERT_TRUE(solver.addClause(clause));
}

void addUnitClause(stp::SATSolver& solver, unsigned var, bool value)
{
  addClauseOrFail(solver, {stp::SATSolver::mkLit(var, !value)});
}

unsigned makeConstantVar(stp::SATSolver& solver, bool value)
{
  const unsigned var = solver.newVar();
  addUnitClause(solver, var, value);
  return var;
}

void addAndEquivalence(stp::SATSolver& solver, unsigned lhs, unsigned rhs,
                       unsigned out)
{
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, true),
                           stp::SATSolver::mkLit(rhs, true),
                           stp::SATSolver::mkLit(out, false)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, false),
                           stp::SATSolver::mkLit(out, true)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(rhs, false),
                           stp::SATSolver::mkLit(out, true)});
}

void addOrEquivalence(stp::SATSolver& solver, unsigned lhs, unsigned rhs,
                      unsigned out)
{
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, true),
                           stp::SATSolver::mkLit(out, false)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(rhs, true),
                           stp::SATSolver::mkLit(out, false)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, false),
                           stp::SATSolver::mkLit(rhs, false),
                           stp::SATSolver::mkLit(out, true)});
}

void addXorEquivalence(stp::SATSolver& solver, unsigned lhs, unsigned rhs,
                       unsigned out)
{
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, true),
                           stp::SATSolver::mkLit(rhs, true),
                           stp::SATSolver::mkLit(out, true)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, true),
                           stp::SATSolver::mkLit(rhs, false),
                           stp::SATSolver::mkLit(out, false)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, false),
                           stp::SATSolver::mkLit(rhs, true),
                           stp::SATSolver::mkLit(out, false)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(lhs, false),
                           stp::SATSolver::mkLit(rhs, false),
                           stp::SATSolver::mkLit(out, true)});
}

void addNotEquivalence(stp::SATSolver& solver, unsigned input, unsigned out)
{
  addClauseOrFail(solver, {stp::SATSolver::mkLit(input, true),
                           stp::SATSolver::mkLit(out, true)});
  addClauseOrFail(solver, {stp::SATSolver::mkLit(input, false),
                           stp::SATSolver::mkLit(out, false)});
}

void buildRippleCarryAdder(stp::SATSolver& solver,
                           const std::vector<unsigned>& a,
                           const std::vector<unsigned>& b,
                           std::vector<unsigned>& sum,
                           bool initial_carry = false,
                           unsigned* final_carry = nullptr)
{
  ASSERT_EQ(a.size(), b.size());
  const unsigned width = static_cast<unsigned>(a.size());
  sum.clear();
  sum.reserve(width);

  unsigned carry_in = makeConstantVar(solver, initial_carry);
  for (unsigned i = 0; i < width; ++i)
  {
    const unsigned lhs = a.at(i);
    const unsigned rhs = b.at(i);

    const unsigned partial = solver.newVar();
    addXorEquivalence(solver, lhs, rhs, partial);

    const unsigned sum_bit = solver.newVar();
    addXorEquivalence(solver, partial, carry_in, sum_bit);

    const unsigned and_ab = solver.newVar();
    addAndEquivalence(solver, lhs, rhs, and_ab);

    const unsigned and_carry_partial = solver.newVar();
    addAndEquivalence(solver, carry_in, partial, and_carry_partial);

    const unsigned carry_out = solver.newVar();
    addOrEquivalence(solver, and_ab, and_carry_partial, carry_out);

    sum.push_back(sum_bit);
    carry_in = carry_out;
  }
  if (final_carry != nullptr)
    *final_carry = carry_in;
}

void buildRippleBorrowSubtractor(stp::SATSolver& solver,
                                 const std::vector<unsigned>& minuend,
                                 const std::vector<unsigned>& subtrahend,
                                 std::vector<unsigned>& difference,
                                 unsigned& final_borrow)
{
  ASSERT_EQ(minuend.size(), subtrahend.size());
  const unsigned width = static_cast<unsigned>(minuend.size());
  difference.clear();
  difference.reserve(width);

  unsigned borrow_in = makeConstantVar(solver, false);
  for (unsigned i = 0; i < width; ++i)
  {
    const unsigned lhs = minuend.at(i);
    const unsigned rhs = subtrahend.at(i);

    const unsigned partial = solver.newVar();
    addXorEquivalence(solver, lhs, rhs, partial);

    const unsigned diff_bit = solver.newVar();
    addXorEquivalence(solver, partial, borrow_in, diff_bit);
    difference.push_back(diff_bit);

    const unsigned not_lhs = solver.newVar();
    addNotEquivalence(solver, lhs, not_lhs);

    const unsigned rhs_or_borrow = solver.newVar();
    addOrEquivalence(solver, rhs, borrow_in, rhs_or_borrow);

    const unsigned term1 = solver.newVar();
    addAndEquivalence(solver, not_lhs, rhs_or_borrow, term1);

    const unsigned term2 = solver.newVar();
    addAndEquivalence(solver, rhs, borrow_in, term2);

    const unsigned borrow_out = solver.newVar();
    addOrEquivalence(solver, term1, term2, borrow_out);

    borrow_in = borrow_out;
  }
  final_borrow = borrow_in;
}

void buildManualAddition(stp::SATSolver& solver,
                         const std::vector<unsigned>& lhs,
                         const std::vector<unsigned>& rhs,
                         std::vector<unsigned>& out)
{
  buildRippleCarryAdder(solver, lhs, rhs, out);
}

void buildManualSubtraction(stp::SATSolver& solver,
                            const std::vector<unsigned>& lhs,
                            const std::vector<unsigned>& rhs,
                            std::vector<unsigned>& out)
{
  ASSERT_EQ(lhs.size(), rhs.size());
  const unsigned width = static_cast<unsigned>(lhs.size());

  std::vector<unsigned> not_rhs;
  not_rhs.reserve(width);
  for (const unsigned bit : rhs)
  {
    const unsigned not_bit = solver.newVar();
    addNotEquivalence(solver, bit, not_bit);
    not_rhs.push_back(not_bit);
  }

  const unsigned zero = makeConstantVar(solver, false);
  const unsigned one = makeConstantVar(solver, true);

  std::vector<unsigned> one_vector(width, zero);
  one_vector[0] = one;

  std::vector<unsigned> neg_rhs;
  buildRippleCarryAdder(solver, not_rhs, one_vector, neg_rhs);

  buildRippleCarryAdder(solver, lhs, neg_rhs, out);
}

void buildManualMultiplication(stp::SATSolver& solver,
                               const std::vector<unsigned>& lhs,
                               const std::vector<unsigned>& rhs,
                               std::vector<unsigned>& out)
{
  ASSERT_EQ(lhs.size(), rhs.size());
  const unsigned width = static_cast<unsigned>(lhs.size());

  const unsigned zero = makeConstantVar(solver, false);
  std::vector<unsigned> accumulator(width, zero);

  for (unsigned i = 0; i < width; ++i)
  {
    std::vector<unsigned> partial(width, zero);
    for (unsigned k = i; k < width; ++k)
    {
      const unsigned x_index = k - i;
      const unsigned and_var = solver.newVar();
      addAndEquivalence(solver, lhs.at(x_index), rhs.at(i), and_var);
      partial[k] = and_var;
    }

    std::vector<unsigned> new_accumulator;
    buildRippleCarryAdder(solver, accumulator, partial, new_accumulator);
    accumulator = std::move(new_accumulator);
  }

  out = std::move(accumulator);
}

void buildManualDivision(stp::SATSolver& solver,
                         const std::vector<unsigned>& dividend,
                         const std::vector<unsigned>& divisor,
                         std::vector<unsigned>& quotient)
{
  ASSERT_EQ(dividend.size(), divisor.size());
  const unsigned width = static_cast<unsigned>(dividend.size());
  const unsigned extended_width = width + 1;

  const unsigned zero = makeConstantVar(solver, false);

  std::vector<unsigned> remainder(extended_width, zero);

  std::vector<unsigned> divisor_ext(extended_width);
  for (unsigned i = 0; i < width; ++i)
    divisor_ext[i] = divisor.at(i);
  divisor_ext[extended_width - 1] = zero;

  quotient.assign(width, zero);

  for (unsigned i = width; i-- > 0;)
  {
    std::vector<unsigned> candidate(extended_width);
    candidate[0] = dividend.at(i);
    for (unsigned bit = 1; bit < extended_width; ++bit)
      candidate[bit] = remainder[bit - 1];

    std::vector<unsigned> difference;
    unsigned borrow = 0;
    buildRippleBorrowSubtractor(solver, candidate, divisor_ext, difference,
                                borrow);
    const unsigned no_borrow = solver.newVar();
    addNotEquivalence(solver, borrow, no_borrow);
    quotient[i] = no_borrow;

    std::vector<unsigned> new_remainder(extended_width);
    for (unsigned bit = 0; bit < extended_width; ++bit)
    {
      const unsigned keep_term = solver.newVar();
      addAndEquivalence(solver, borrow, candidate.at(bit), keep_term);

      const unsigned take_term = solver.newVar();
      addAndEquivalence(solver, no_borrow, difference.at(bit), take_term);

      const unsigned remainder_bit = solver.newVar();
      addOrEquivalence(solver, keep_term, take_term, remainder_bit);
      new_remainder[bit] = remainder_bit;
    }

    remainder = std::move(new_remainder);
  }
}

unsigned buildOrChain(stp::SATSolver& solver,
                      const std::vector<unsigned>& inputs)
{
  assert(!inputs.empty());
  if (inputs.size() == 1)
    return inputs.front();

  unsigned current = inputs.front();
  for (size_t i = 1; i < inputs.size(); ++i)
  {
    const unsigned next = inputs.at(i);
    const unsigned out = solver.newVar();
    addOrEquivalence(solver, current, next, out);
    current = out;
  }

  return current;
}

using StpBuilder =
    std::function<ASTNode(stp::STPMgr&, ASTNode, ASTNode, unsigned)>;

void runOperationWidth(unsigned width, const StpBuilder& stp_builder,
                       const ManualBuilder& builder)
{
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf(*(mgr.hashingNodeFactory), mgr);
  mgr.defaultNodeFactory = &snf;

  stp::SubstitutionMap substitution_map(&mgr);
  stp::Simplifier simplifier(&mgr, &substitution_map);
  stp::ArrayTransformer array_transformer(&mgr, &simplifier);

  ASTNode x = mgr.CreateSymbol("x", 0, width);
  ASTNode y = mgr.CreateSymbol("y", 0, width);
  ASTNode z = mgr.CreateSymbol("z", 0, width);

  ASTNode stp_result = stp_builder(mgr, x, y, width);
  ASTNode equality = mgr.CreateNode(stp::EQ, stp_result, z);

  stp::ToSATAIG tosat(&mgr, &array_transformer);
  stp::SimplifyingMinisat solver;

  Cnf_Dat_t* cnf = tosat.bitblast(equality, false);
  ASSERT_NE(cnf, nullptr);
  tosat.add_cnf_to_solver(solver, cnf);
  tosat.release_cnf_memory(cnf);

  const auto& sat_map = tosat.SATVar_to_SymbolIndexMap();

  auto x_it = sat_map.find(x);
  ASSERT_TRUE(x_it != sat_map.end());
  auto y_it = sat_map.find(y);
  ASSERT_TRUE(y_it != sat_map.end());
  auto z_it = sat_map.find(z);
  ASSERT_TRUE(z_it != sat_map.end());

  const std::vector<unsigned>& x_bits = x_it->second;
  const std::vector<unsigned>& y_bits = y_it->second;
  const std::vector<unsigned>& z_bits = z_it->second;

  ASSERT_EQ(x_bits.size(), width);
  ASSERT_EQ(y_bits.size(), width);
  ASSERT_EQ(z_bits.size(), width);

  std::vector<unsigned> manual_result;
  builder(solver, x_bits, y_bits, manual_result);
  ASSERT_EQ(manual_result.size(), width);

  std::vector<unsigned> diff_bits;
  diff_bits.reserve(width);
  for (unsigned i = 0; i < width; ++i)
  {
    const unsigned diff = solver.newVar();
    addXorEquivalence(solver, manual_result.at(i), z_bits.at(i), diff);
    diff_bits.push_back(diff);
  }

  const unsigned mismatch = buildOrChain(solver, diff_bits);
  addUnitClause(solver, mismatch, true);

  bool timeout_expired = false;
  const bool sat = solver.solve(timeout_expired);

  ASSERT_FALSE(timeout_expired);
  ASSERT_FALSE(sat);
}

void runAdditionWidth(unsigned width)
{
  runOperationWidth(
      width,
      [](stp::STPMgr& mgr, ASTNode x, ASTNode y, unsigned w) {
        return mgr.CreateTerm(stp::BVPLUS, w, x, y);
      },
      &buildManualAddition);
}

void runSubtractionWidth(unsigned width)
{
  runOperationWidth(
      width,
      [](stp::STPMgr& mgr, ASTNode x, ASTNode y, unsigned w) {
        ASTNode neg_y = mgr.CreateTerm(stp::BVUMINUS, w, y);
        return mgr.CreateTerm(stp::BVPLUS, w, x, neg_y);
      },
      &buildManualSubtraction);
}

void runMultiplicationWidth(unsigned width)
{
  runOperationWidth(
      width,
      [](stp::STPMgr& mgr, ASTNode x, ASTNode y, unsigned w) {
        return mgr.CreateTerm(stp::BVMULT, w, x, y);
      },
      &buildManualMultiplication);
}

void runDivisionWidth(unsigned width)
{
  runOperationWidth(
      width,
      [](stp::STPMgr& mgr, ASTNode x, ASTNode y, unsigned w) {
        return mgr.CreateTerm(stp::BVDIV, w, x, y);
      },
      &buildManualDivision);
}

} // namespace

TEST(BvArithmeticCnfTest, BvPlusMatchesRippleCarryForFiveToTenBits)
{
  for (unsigned width = 5; width <= 10; ++width)
  {
    SCOPED_TRACE(width);
    runAdditionWidth(width);
  }
}

TEST(BvArithmeticCnfTest, BvSubMatchesTwosComplementForFiveToTenBits)
{
  for (unsigned width = 5; width <= 10; ++width)
  {
    SCOPED_TRACE(width);
    runSubtractionWidth(width);
  }
}

TEST(BvArithmeticCnfTest, BvMultMatchesShiftAddForFiveToEightBits)
{
  for (unsigned width = 5; width <= 8; ++width)
  {
    SCOPED_TRACE(width);
    runMultiplicationWidth(width);
  }
}

TEST(BvArithmeticCnfTest, BvDivMatchesRestoringDivisionForFiveToSevenBits)
{
  for (unsigned width = 5; width <= 7; ++width)
  {
    SCOPED_TRACE(width);
    runDivisionWidth(width);
  }
}
