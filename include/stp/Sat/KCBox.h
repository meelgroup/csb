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

#ifndef KCBOX_H_
#define KCBOX_H_

#include "stp/Sat/SATSolver.h"

#include <cstdint>
#include <vector>

namespace stp
{

// KCBox provides both counting and sampling functionality. This wrapper keeps
// the interface consistent with other SAT back-ends used by STP.
#if defined(__GNUC__) || defined(__clang__)
class __attribute__((visibility("default"))) KCBox : public SATSolver
#else
class KCBox : public SATSolver
#endif
{
public:
  KCBox(uint64_t sampler_seed, bool enable_sampling, bool enable_counting);
  ~KCBox() override;

  bool addClause(const vec_literals& ps) override;
  bool okay() const override;
  bool solve(bool& timeout_expired) override;

  uint8_t modelValue(uint32_t x) const override;
  uint32_t newProjVar(uint32_t x) override;
  uint32_t newVar() override;

  void setVerbosity(int v) override;
  unsigned long nVars() const override;
  void printStats() const override;

  lbool true_literal() override { return ((uint8_t)1); }
  lbool false_literal() override { return ((uint8_t)-1); }
  lbool undef_literal() override { return ((uint8_t)0); }

  void setVarWeight(uint32_t var, double weight) override;
  void setNegWeight(uint32_t var, double weight) override;

private:
  void ensureWeightSize(size_t var_index);

  uint64_t seed;
  uint32_t max_var;
  bool sampling_enabled;
  bool counting_enabled;
  std::vector<std::vector<int>> clauses;
  std::vector<double> weights;
  std::vector<double> neg_weights;
  std::vector<uint32_t> projected_vars;
  std::vector<int8_t> sampled_assignment;
  bool sample_available = false;
  bool weights_specified = false;
  int verbosity = 0;
};

} // namespace stp

#endif
