/********************************************************************
 * AUTHORS: Arijit Shaw
 * AUTHORS: Mate Soos, Andrew V. Jones
 *
 * BEGIN DATE: November, 2013
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

#include "stp/Sat/CMSGen.h"
#include "cmsgen/cmsgen.h"
#include "cmsgen/solvertypesmini.h"
#include <algorithm>
#include <unordered_set>
using std::vector;

namespace stp
{

void CMSGenC::enableRefinement(const bool enable)
{
  // might break if we simplify with refinement enabled..
  if (enable)
  {
    s->set_no_simplify();
  }
}

CMSGenC::CMSGenC(uint32_t *seed)
{
  s = new CMSGen::SATSolver(NULL,NULL, seed);
  temp_cl = (void*)new vector<CMSGen::Lit>;
  // s->set_seed(seed);
  // TODO - set seed
}

CMSGenC::~CMSGenC()
{
  delete s;
  vector<CMSGen::Lit>* real_temp_cl = (vector<CMSGen::Lit>*)temp_cl;
  delete real_temp_cl;
}

void CMSGenC::setMaxConflicts(int64_t _max_confl)
{
  max_confl = _max_confl;
}

void CMSGenC::setMaxTime(int64_t _max_time)
{
  max_time = _max_time;
}

bool CMSGenC::addClause(
    const vec_literals& ps) // Add a clause to the solver.
{
  // Cryptominisat uses a slightly different vec class.
  // Cryptominisat uses a slightly different Lit class too.

  vector<CMSGen::Lit>& real_temp_cl = *(vector<CMSGen::Lit>*)temp_cl;
  real_temp_cl.clear();
  for (int i = 0; i < ps.size(); i++)
  {
    real_temp_cl.push_back(CMSGen::Lit(var(ps[i]), sign(ps[i])));
  }

  return s->add_clause(real_temp_cl);
}

bool CMSGenC::okay()
    const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

bool CMSGenC::solve(bool& timeout_expired) // Search without assumptions.
{
  if (max_confl > 0) {
     s->set_max_confl(std::max(max_confl - s->get_sum_conflicts(), (uint64_t)1));
  }

  /*
   * STP uses -1 for a value of "no timeout" -- this means that we only set the
   * timeout _in the SAT solver_ if the value is >= 0. This avoids us
   * accidentally setting a large limit (or one in the past).
   */
  if (max_time > 0) {
     s->set_max_time(max_time);
  }

  s->set_sampling_vars(&sampling_vars_orig);

  CMSGen::lbool ret = s->solve();
  if (ret == CMSGen::l_Undef)
  {
    timeout_expired = true;
  }
  return ret == CMSGen::l_True;
}

uint8_t CMSGenC::modelValue(uint32_t x) const
{
  return (s->get_model().at(x) == CMSGen::l_True);
}

uint32_t CMSGenC::newProjVar(uint32_t x)
{
  sampling_vars_orig.push_back(x);
  return 1;
}

uint32_t CMSGenC::newVar()
{
  s->new_var();
  return s->nVars() - 1;
}

void CMSGenC::setVerbosity(int v)
{
  s->set_verbosity(v);
}

unsigned long CMSGenC::nVars() const
{
  return s->nVars();
}

void CMSGenC::printStats() const
{
  // s->printStats();
}

void CMSGenC::solveAndDump()
  {
     bool t;
     solve(t);
  }



// Count how many literals/bits get fixed subject to the assumptions..
uint32_t CMSGenC::getFixedCountWithAssumptions(const stp::SATSolver::vec_literals& assumps, const std::unordered_set<unsigned>& literals )
{
  std::cout << "ERROR: Did not expect to reach here in sampling" << std::endl;
  assert(false);
  const uint64_t conf = s->get_sum_conflicts();
  assert(conf == 0);

  // s->simplify(); TODO AS: this is not implemented yet in CMSGen, so we just assume it is satisfiable.
  // const CMSGen::lbool r = CMSGen::lit_Undef;
  //  =  s->simplify();

  // Add the assumptions are clauses.
  vector<CMSGen::Lit>& real_temp_cl = *(vector<CMSGen::Lit>*)temp_cl;
  for (int i = 0; i < assumps.size(); i++)
  {
    real_temp_cl.clear();
    real_temp_cl.push_back(CMSGen::Lit(var(assumps[i]), sign(assumps[i])));
    s->add_clause(real_temp_cl);
  }


  //std::cerr << assumps.size() << " assumptions" << std::endl;

  uint32_t assigned = 0;
  // std::vector<CMSGen::Lit> zero = s->get_zero_assigned_lits();
  // for (CMSGen::Lit l : zero)
  // {
  //     if (literals.find(l.var()) != literals.end())
  //       assigned++;
  // }

  //std::cerr << assigned << " assignments at end" <<std::endl;

  // The assumptions are each single literals (corresponding to bits) that are true/false.
  // so in the result they should be all be set
  assert(assumps.size() >= 0);
  assert(assigned >= static_cast<uint32_t>(assumps.size()));
  assert(s->get_sum_conflicts() == conf ); // no searching, so no conflicts.
  // assert(CMSGen::l_False != r); // always satisfiable.

  return assigned;
}



} //end namespace stp
