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
#include <unordered_map>
#include <unordered_set>
using std::vector;

using namespace CMSat;
using namespace UniGen; // namespace in UniGen library

using std::cout;
using std::endl;

namespace stp
{

static vector<vector<int>> unigen_models;
static size_t next_model_index = 0;
static std::vector<uint32_t> free_vars;
static std::vector<uint32_t> cached_sampling_vars;
static std::unordered_map<uint32_t, size_t> sat_var_to_sample_index;

void mycallback(const std::vector<int>& solution, void* data)
{
  // vector<vector<int>>* unigen_models = (vector<vector<int>>*)data;
  /* for (auto s : solution) std::cout << (s>0 ? "1" : "0"); */
  /* std::cout << std::endl; */
  // std::cout << "c [stp->apxmc] model callback: " << solution.size() << " :";
  // for (size_t i = 0; i < solution.size(); ++i)
  // {
  //   std::cout  << solution[i];
  // }
  //   std::cout   << std::endl;

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
    : appmc(fg), cnf(fg), seed(unisamp_seed), samples_generated(_samples_generated),
      samples_needed(_samples_needed), unisamp_ran(false), unigen(nullptr),
      arjun(nullptr)
{
  if (_samples_generated == 0)
  {
    unigen_models.clear();
    cached_sampling_vars.clear();
    next_model_index = 0;
  }
  else
  {
    next_model_index = _samples_generated;
  }

  unigen = std::make_unique<UniGen::UniG>(&appmc);
  arjun = std::make_unique<ArjunNS::Arjun>();
  unigen->set_callback(mycallback, &unigen_models);
  appmc.set_verbosity(0);
  arjun->set_verb(0);
  arjun->set_or_gate_based(0);
  arjun->set_xor_gates_based(0);
  arjun->set_ite_gate_based(0);
  arjun->set_irreg_gate_based(0);
  unigen->set_verbosity(0);
  appmc.set_seed(seed);
  temp_cl = (void*)new vector<CMSat::Lit>;

  if (samples_needed == 0)
    samples_needed = 1;

  unisamp_ran = !unigen_models.empty();
}

UniSamp::~UniSamp()
{
  // delete unigen;
  // delete arjun;
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
  cnf.add_clause(real_temp_cl);
  return true;
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

  timeout_expired = false;

  if (!unisamp_ran || next_model_index >= unigen_models.size())
  {
    unigen_models.clear();
      std::unique_ptr<CMSat::Field> cnt = cnf.multiplier_weight->dup();
    const CMSat::Field* ptr = cnt.get();
    const ArjunNS::FMpz* mult = dynamic_cast<const ArjunNS::FMpz*>(ptr);
    double mult_val = mult->val.get_d();
    std::cout << "c [stp->apxmc] sampling vars [arjun] "
              << cnf.get_sampl_vars().size() << ", multipler weight " << mult_val
              <<  std::endl;
  cnf.set_sampl_vars(sampling_vars_orig);
  if (cnf.get_sampl_vars().empty())
  {
    etof_conf.all_indep = true;
    std::vector<uint32_t> all_vars;
    all_vars.reserve(cnf.nVars());
    for (uint32_t i = 0; i < cnf.nVars(); ++i)
      all_vars.push_back(i);
    cnf.set_sampl_vars(all_vars, true);
    std::cout << "c [stp->apxmc] no sampling vars, setting all (" << cnf.nVars() << ") sampling vars \n";
  }
  else
  {
    std::cout << "c [stp->apxmc] sampling vars [input] " << cnf.get_sampl_vars().size() << std::endl;
    etof_conf.all_indep = (cnf.get_sampl_vars().size() == cnf.nVars());
    if (!cnf.get_opt_sampl_vars_set())
      cnf.set_opt_sampl_vars(cnf.get_sampl_vars());
  }

  if (arjun)
    arjun->set_verb(0);
  std::cout << "c [stp->apxmc] Arjun solving instance with " << cnf.nVars()
            << " variables, " << cnf.clauses.size() << " clauses "
            << sampling_vars_orig.size() << " projection vars" << std::endl;

  // arjun->standalone_minimize_indep(cnf, etof_conf.all_indep);

  std::cout << "c [stp->apxmc] ApxMC solving instance with " << cnf.nVars()
            << " variables, " << cnf.clauses.size() << " clauses "
            << std::endl;
    // const CMSat::Field* ptr = cnf.multiplier_weight.get();
     cnt = cnf.multiplier_weight->dup();
   ptr = cnt.get();

     mult = dynamic_cast<const ArjunNS::FMpz*>(ptr);
   mult_val = mult->val.get_d();

    std::cout << "c [stp->apxmc] sampling vars [arjun] "
            << cnf.get_sampl_vars().size() << ", multipler weight " << mult_val
            <<  std::endl;




  appmc.new_vars(cnf.nVars());


  appmc.set_sampl_vars(cnf.sampl_vars);
  for (const auto& cl : cnf.clauses)
    appmc.add_clause(cl);
  for (const auto& cl : cnf.red_clauses)
    appmc.add_red_clause(cl);
  appmc.set_multiplier_weight(cnf.multiplier_weight);

      ApproxMC::SolCount sol_count;
    sol_count = appmc.count();
    // appmc.print_stats(start_time);
    // std::cout << "c o [appmc+arjun] Total time: " << (cpu_time() - start_time) << std::endl;
    std::cout << "c [stp->apxmc] Count: " << sol_count.cellSolCount
              << "*2**" << sol_count.hashCount << std::endl
              << " * " <<  mult_val << std::endl;



    unigen->set_verbosity(0);
    unigen->set_verb_sampler_cls(0);
    unigen->set_kappa(0.1);
    unigen->set_multisample(true);
    unigen->set_full_sampling_vars(sampling_vars_orig);

    unigen_models.clear();
    unigen->sample(&sol_count, samples_needed);
    unisamp_ran = true;

    for (size_t i = 0; i < sampling_vars_orig.size(); ++i)
    {
      if(std::find(cnf.sampl_vars.begin(), cnf.sampl_vars.end(), sampling_vars_orig[i]) == cnf.sampl_vars.end()){
        free_vars.push_back(sampling_vars_orig[i]);
      }
    }
    std::cout << "c free vars: " << free_vars.size() << std::endl;
    std::cout << "c [stp->apxmc] samples generated: " << unigen_models.size() << std::endl;
  for (size_t i = 0; i < sampling_vars_orig.size(); ++i)
    {
      uint32_t var = static_cast<uint32_t>(std::abs(unigen_models[0][i]));
      // std::cout << "c [stp->apxmc] sample var " << sampling_vars_orig[i] << " corresponds to SAT var " << var << std::endl;
      sat_var_to_sample_index[sampling_vars_orig[i]] = i;
    }
  }
  else if (!cached_sampling_vars.empty())
  {
    sampling_vars_current = cached_sampling_vars;

  }

  if (unigen_models.empty())
  {
    return false;
  }

  const size_t current_index =
      std::min(next_model_index, unigen_models.size() - 1);
  samples_generated++;
  next_model_index = current_index + 1;
  // std::cout << "c [stp->apxmc] returning sample " << current_index << " :";
  // for (size_t i = 0; i < sampling_vars_orig.size(); ++i)
  //   {
  //     std::cout << unigen_models[next_model_index - 1][i] << " ";
  //   }
  //   std::cout << std::endl;
  return true;
}

uint8_t UniSamp::modelValue(uint32_t x) const
{
  if (!unisamp_ran || unigen_models.empty() || samples_generated == 0)
  {
    return (uint8_t)0;
  }
  // if (free_vars.size() > 0 && std::find(free_vars.begin(), free_vars.end(), x) != free_vars.end())
  // {
  //   return (uint8_t)(rand() % 2);
  // }
  const size_t sample_index = next_model_index == 0
                                  ? std::min<size_t>(0, unigen_models.size() - 1)
                                  : std::min<size_t>(next_model_index - 1,
                                                     unigen_models.size() - 1);
  const auto& sample = unigen_models.at(sample_index);
  // std::cout << "c [stp->apxmc] modelValue for var " << x << " in sample index " << sample_index << std::endl;

  const auto it = sat_var_to_sample_index.find(x);
  if (it == sat_var_to_sample_index.end())
    return (uint8_t)0;

  const size_t idx = it->second;
  if (idx >= sample.size())
    return (uint8_t)0;

  return sample.at(idx) > 0 ? (uint8_t)1 : (uint8_t)-1;
}

uint32_t UniSamp::newProjVar(uint32_t x)
{
  sampling_vars_orig.push_back(x);
  return 1;
}

uint32_t UniSamp::newVar()
{
  cnf.new_var();
  return cnf.nVars() - 1;
}

void UniSamp::setVerbosity(int v)
{
  appmc.set_verbosity(v);
  unigen->set_verbosity(v);
  arjun->set_verb(v);
}

unsigned long UniSamp::nVars() const
{
  return cnf.nVars();
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
