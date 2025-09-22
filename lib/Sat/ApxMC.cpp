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

#include "stp/Sat/ApxMC.h"
#include "approxmc/approxmc.h"
#include <algorithm>
#include <gmpxx.h>
#include <unordered_set>

using std::vector;

using namespace CMSat;
using namespace ApxMC; // namespace in appmc library

namespace stp
{

void ApxMC::enableRefinement(const bool enable)
{
  // might break if we simplify with refinement enabled..
  //   if (enable)
  //   {
  //     s->set_no_simplify_at_startup();
  //   }
}

ApxMC::ApxMC(uint64_t unisamp_seed)
    : appmc(fg), cnf(fg)
{
  arjun = new ArjunNS::Arjun;
  seed = unisamp_seed;
  arjun->set_verb(0);
  temp_cl = (void*)new vector<CMSat::Lit>;
}

ApxMC::~ApxMC()
{
  delete arjun;
  vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
  delete real_temp_cl;
}

void ApxMC::setMaxConflicts(int64_t _max_confl)
{
  max_confl = _max_confl;
}

void ApxMC::setMaxTime(int64_t _max_time)
{
  max_time = _max_time;
}

bool ApxMC::addClause(const vec_literals& ps) // Add a clause to the solver.
{
  // Cryptominisat uses a slightly different vec class.
  // Cryptominisat uses a slightly different Lit class too.

  vector<CMSat::Lit>& cl = *(vector<CMSat::Lit>*)temp_cl;
  cl.clear();
  for (int i = 0; i < ps.size(); i++)
  {
    cl.push_back(CMSat::Lit(var(ps[i]), sign(ps[i])));
  }
  cnf.set_weighted(false);
  cnf.add_clause(cl);
  return true;
}

bool ApxMC::okay() const // FALSE means solver is in a conflicting state
{
  //return appmc.okay();
  return true; //TODO AS: implement well
}

bool ApxMC::solve(bool& timeout_expired) // Search without assumptions.
{

  /*
   * STP uses -1 for a value of "no timeout" -- this means that we only set the
   * timeout _in the SAT solver_ if the value is >= 0. This avoids us
   * accidentally setting a large limit (or one in the past).
   */

  // CMSat::lbool ret = s->solve(); // TODO AS
  cnf.set_sampl_vars(sampling_vars_orig);
  std::cout << "c [stp->appmc] ApxMC solving instance with " << cnf.nVars()
            << " variables, " << sampling_vars_orig.size()
            << " projection vars" << std::endl;

  appmc.set_seed(seed);
  appmc.set_verbosity(0);
  arjun->set_verb(0);
  // std::cout << "c Arjun SHA revision " << arjun->get_version_info()
  //           << std::endl;

  ArjunNS::SimpConf sc;
  sc.appmc = true;
  sc.oracle_vivify = true;
  sc.oracle_vivify_get_learnts = true;
  sc.oracle_sparsify = false;
  sc.iter1 = 2;
  sc.iter2 = 0;

  auto ret = arjun->standalone_get_simplified_cnf(cnf, sc);

  std::vector<uint32_t> sampling_vars = ret.sampl_vars;
  appmc.new_vars(ret.nvars);
  for (const auto& cl : ret.clauses)
    appmc.add_clause(cl);
  for (const auto& cl : ret.red_clauses)
    appmc.add_clause(cl);

  appmc.set_multiplier_weight(ret.multiplier_weight);

  std::cout << "c [appmc->arjun] sampling var size [from arjun] "
            << sampling_vars.size() << "\n";

  appmc.set_sampl_vars(sampling_vars);

  auto sol_count = appmc.count();

  // use gmp to get the absolute count of solutions
  mpz_class result;
  mpz_class cellSolCount_gmp(sol_count.cellSolCount);
  mpz_mul_2exp(result.get_mpz_t(), cellSolCount_gmp.get_mpz_t(),
               sol_count.hashCount);

  const CMSat::Field* ptr = appmc.get_multiplier_weight().get();
  mpq_class multiplier(1);
  if (ptr != nullptr)
  {
    if (const ArjunNS::FMpq* mult = dynamic_cast<const ArjunNS::FMpq*>(ptr))
    {
      multiplier = mult->val;
    }
  }
  mpq_class final = multiplier * result;

  std::cout << "s mc " << final << std::endl;

  exit(0);
  return true;
}

uint8_t ApxMC::modelValue(uint32_t x) const
{
  //   if (appmc_models[0].size() < sampling_vars.size())
  //     std::cout << "c [stp->appmc] ERROR! found model size is not large enough\n";
  return true;
}

uint32_t ApxMC::newProjVar(uint32_t x)
{
  sampling_vars_orig.push_back(x);
  return 1;
}

uint32_t ApxMC::newVar()
{
  cnf.new_var();
  return cnf.nVars() - 1;
}

void ApxMC::setVerbosity(int v)
{
  appmc.set_verbosity(v);
  arjun->set_verb(v);
}

unsigned long ApxMC::nVars() const
{
  return cnf.nVars();
}

void ApxMC::printStats() const
{
  // s->printStats();
}

void ApxMC::solveAndDump()
{
  bool t;
  solve(t);
  //s->open_file_and_dump_irred_clauses("clauses.txt");
}

// Count how many literals/bits get fixed subject to the assumptions..
uint32_t ApxMC::getFixedCountWithAssumptions(
    const stp::SATSolver::vec_literals& assumps,
    const std::unordered_set<unsigned>& literals)
{
  /* TODO AS skip all?
  const uint64_t conf = 0; // TODO AS: s->get_sum_conflicts();
  assert(conf == 0);


  // const CMSat::lbool r = s->simplify();  TODO AS


  // Add the assumptions are clauses.
  vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
  for (int i = 0; i < assumps.size(); i++)
  {
    real_temp_cl.clear();
    real_temp_cl.push_back(CMSat::Lit(var(assumps[i]), sign(assumps[i])));
    appmc.add_clause(real_temp_cl);
  }


  //std::cerr << assumps.size() << " assumptions" << std::endl;

  std::vector<CMSat::Lit> zero = s->get_zero_assigned_lits();
  for (CMSat::Lit l : zero)
  {
      if (literals.find(l.var()) != literals.end())
        assigned++;
  }



  //std::cerr << assigned << " assignments at end" <<std::endl;

  // The assumptions are each single literals (corresponding to bits) that are true/false.
  // so in the result they should be all be set
  assert(assumps.size() >= 0);
  assert(assigned >= static_cast<uint32_t>(assumps.size()));
  assert(s->get_sum_conflicts() == conf ); // no searching, so no conflicts.
  assert(CMSat::l_False != r); // always satisfiable.
  */

  uint32_t assigned = 0;

  return assigned;
}

} //end namespace stp
