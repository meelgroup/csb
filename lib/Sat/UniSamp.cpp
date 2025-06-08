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

#include "stp/Sat/UniSamp.h"
#include "approxmc/approxmc.h"
#include "unigen/unigen.h"
#include <algorithm>
#include <unordered_set>
using std::vector;

using namespace CMSat;
using namespace UniGen; // namespace in UniGen library

using std::cout;
using std::endl;

namespace stp
{

static vector<vector<int>> unigen_models;

void mycallback(const std::vector<int>& solution, void* data)
{
  // vector<vector<int>>* unigen_models = (vector<vector<int>>*)data;
  /* for (auto s : solution) std::cout << (s>0 ? "1" : "0"); */
  /* std::cout << std::endl; */
  unigen_models.push_back(solution);
}

void UniSamp::enableRefinement(const bool enable)
{
  // might break if we simplify with refinement enabled..
  //   if (enable)
  //   {
  //     s->set_no_simplify_at_startup();
  //   }
}

UniSamp::UniSamp(uint64_t unisamp_seed, uint64_t _samples_needed,
                 uint64_t _samples_generated)
{

  appmc = new ApproxMC::AppMC;

  unigen = new UniG(appmc);
  arjun = new ArjunNS::Arjun;
  seed = unisamp_seed;
  samples_needed = _samples_needed;
  samples_generated = _samples_generated;
  // unisamp_ran = false;
  unigen->set_callback(mycallback, &unigen_models);
  appmc->set_verbosity(0);
  arjun->set_verb(0);
  unigen->set_verbosity(0);
  appmc->set_seed(seed);

  // s->log_to_file("stp.cnf");
  //s->set_num_threads(num_threads);
  //s->set_default_polarity(false);
  //s->set_allow_otf_gauss();
  temp_cl = (void*)new vector<CMSat::Lit>;
}

UniSamp::~UniSamp()
{
  delete unigen;
  vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
  delete real_temp_cl;
}

void UniSamp::setMaxConflicts(int64_t _max_confl)
{
  max_confl = _max_confl;
}

void UniSamp::setMaxTime(int64_t _max_time)
{
  max_time = _max_time;
}

bool UniSamp::addClause(const vec_literals& ps) // Add a clause to the solver.
{
  vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
  real_temp_cl.clear();
  for (int i = 0; i < ps.size(); i++)
  {
    real_temp_cl.push_back(CMSat::Lit(var(ps[i]), sign(ps[i])));
  }
  /* cout << "c Adding clause to arjun " << real_temp_cl << " 0" << endl; */
  return arjun->add_clause(real_temp_cl);
}

bool UniSamp::okay() const // FALSE means solver is in a conflicting state
{
  //return a->okay();
  return true; //TODO AS: implement well
}

bool UniSamp::solve(bool& timeout_expired) // Search without assumptions.
{

  /*
   * STP uses -1 for a value of "no timeout" -- this means that we only set the
   * timeout _in the SAT solver_ if the value is >= 0. This avoids us
   * accidentally setting a large limit (or one in the past).
   */

  // CMSat::lbool ret = s->solve(); // TODO AS
  samples_generated++;
  std::cout << "c [stp->unigen] Generating Sample number " << samples_generated
            << std::endl;
  if (samples_generated > 1)
    return true;

  std::cout << "c [stp->unigen] UniSamp solving instance with "
            << arjun->nVars() << " variables." << std::endl;

  vector<uint32_t> sampling_vars, all_vars;
  for (uint32_t i = 0; i < arjun->nVars(); i++)
    all_vars.push_back(i);

  arjun->set_sampl_vars(sampling_vars_orig);

  const uint32_t orig_num_vars = arjun->nVars();
  appmc->new_vars(orig_num_vars);

  bool ret = true;
  arjun->start_getting_constraints(false);
  vector<Lit> clause;
  while (ret)
  {
    bool is_xor, rhs;
    ret = arjun->get_next_constraint(clause, is_xor, rhs);
    assert(rhs);
    assert(!is_xor);
    if (!ret)
      break;

    bool ok = true;
    for (auto l : clause)
    {
      if (l.var() >= orig_num_vars)
      {
        ok = false;
        break;
      }
    }
    if (ok)
    {
      /* cout << "adding clause to appmc " << clause << endl; */
      appmc->add_clause(clause);
    }
  }
  arjun->end_getting_constraints();
  sampling_vars = arjun->run_backwards();
  auto empty_sampl_vars = arjun->get_empty_sampl_vars();
  delete arjun;

  appmc->set_sampl_vars(sampling_vars);

  std::cout << "c [unigen->arjun] sampling var size [from arjun] "
            << sampling_vars.size() << " orig size "
            << sampling_vars_orig.size() << "\n";

  auto sol_count = appmc->count();
  cout << "c Sol count: " << sol_count.cellSolCount << "*2**"
       << (sol_count.hashCount + empty_sampl_vars.size()) << endl;

  // std::cout << "c [stp->unigen] ApproxMC got count " << sol_count.cellSolCount
  // << "*2**" << sol_count.hashCount << std::endl;
  unigen->set_verbosity(0);
  unigen->set_verb_sampler_cls(0);
  unigen->set_kappa(0.1);
  unigen->set_multisample(false);
  unigen->set_full_sampling_vars(all_vars);
  // unigen->set_empty_sampling_vars(empty_sampl_vars);

  unigen->sample(&sol_count, samples_needed);
  unisamp_ran = true;
  return true;
}

uint8_t UniSamp::modelValue(uint32_t x) const
{
  //   if (unigen_models[0].size() < sampling_vars.size())
  //     std::cout << "c [stp->unigen] ERROR! found model size is not large enough\n";
  if (samples_generated >= unigen_models.size())
  {
    std::cout << "c [stp->unigen] ERROR! samples_generated: "
              << samples_generated
              << " but unigen_models.size(): " << unigen_models.size()
              << std::endl;
    exit(-1);
  }
  return (unigen_models.at(samples_generated).at(x) > 0);
}

uint32_t UniSamp::newProjVar(uint32_t x)
{
  sampling_vars_orig.push_back(x);
  return 1;
}

uint32_t UniSamp::newVar()
{
  arjun->new_var();
  return arjun->nVars() - 1;
}

void UniSamp::setVerbosity(int v)
{
  arjun->set_verbosity(0);
}

unsigned long UniSamp::nVars() const
{
  return arjun->nVars();
}

void UniSamp::printStats() const
{
  // s->printStats();
}

void UniSamp::solveAndDump()
{
  bool t;
  solve(t);
  //s->open_file_and_dump_irred_clauses("clauses.txt");
}

// Count how many literals/bits get fixed subject to the assumptions..
uint32_t UniSamp::getFixedCountWithAssumptions(
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
    a->add_clause(real_temp_cl);
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
