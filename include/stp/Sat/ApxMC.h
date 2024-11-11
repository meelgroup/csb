/********************************************************************
 * AUTHORS: Arijit Shaw
 *
 * BEGIN DATE: November, 2023
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

/*
 * Wraps around ApproxMC.
 */
#ifndef APXMC_H_
#define APXMC_H_

#include "approxmc/approxmc.h"
#include "stp/Sat/SATSolver.h"
#include <arjun/arjun.h>

#include <unordered_set>

using std::vector;

namespace ApxMC
{
class SATSolver;
}

namespace stp
{
#if defined(__GNUC__) || defined(__clang__)
class __attribute__((visibility("default"))) ApxMC : public SATSolver
#else
class ApxMC : public SATSolver
#endif

{
  ApproxMC::AppMC* a;
  ArjunNS::Arjun* arjun;
  uint64_t seed;
  vector<uint32_t> sampling_vars_orig;

public:
  ApxMC(uint64_t unisamp_seed);

  ~ApxMC();

  virtual void setMaxConflicts(int64_t max_confl); // set max solver conflicts

  virtual void setMaxTime(int64_t max_time); // set max solver time in seconds

  bool addClause(const vec_literals& ps); // Add a clause to the solver.

  bool okay() const; // FALSE means solver is in a conflicting state

  bool solve(bool& timeout_expired); // Search without assumptions.

  virtual uint8_t modelValue(uint32_t x) const;

  virtual uint32_t newVar();

  virtual uint32_t newProjVar();

  void setVerbosity(int v);

  unsigned long nVars() const;

  void printStats() const;

  virtual void enableRefinement(const bool enable);

  // nb CryptoMiniSat has different literal values to the other minisats.
  virtual lbool true_literal() { return ((uint8_t)1); }
  virtual lbool false_literal() { return ((uint8_t)-1); }
  virtual lbool undef_literal() { return ((uint8_t)0); }

  uint32_t
  getFixedCountWithAssumptions(const stp::SATSolver::vec_literals& assumps,
                               const std::unordered_set<unsigned>& literals);

  void solveAndDump();

private:
  void* temp_cl;
  int64_t max_confl = 0;
  int64_t max_time = 0; // seconds
};
} // namespace stp

#endif
