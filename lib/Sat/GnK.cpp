/********************************************************************
 * AUTHORS: Arijit Shaw
 *
 * BEGIN DATE: November, 2024
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

#include "stp/Sat/GnK.h"
#include <ganak/ganak.hpp>
#include <arjun/arjun.h>

#include <algorithm>
#include <set>
#include <sstream>
#include <unordered_set>
#include <iomanip>

using std::vector;

using namespace CMSat;
using namespace GnK; // namespace in appmc library

std::vector<GanakInt::Lit> cms_to_ganak_cl(const std::vector<CMSat::Lit>& cl)
{
  std::vector<GanakInt::Lit> ganak_cl;
  ganak_cl.reserve(cl.size());
  for (const auto& l : cl)
    ganak_cl.push_back(GanakInt::Lit(l.var() + 1, !l.sign()));
  return ganak_cl;
}

namespace stp
{

void GnK::enableRefinement(const bool enable)
{
  // might break if we simplify with refinement enabled..
  //   if (enable)
  //   {
  //     s->set_no_simplify_at_startup();
  //   }
}

GnK::GnK(uint64_t unisamp_seed)
    :
      cnf(fg),                                  // init member cnf with fg
      // arjun(new Arjun),                         // init member arjun
      seed(unisamp_seed), temp_cl(nullptr), max_confl(0), max_time(0)
{
  // now allocate temp_cl
  ganak = new Ganak(conf, fg);
  arjun = new ArjunNS::Arjun();
  std::cout << "c [stp->gnk] GnK initialized" << std::endl;
  temp_cl = new std::vector<CMSat::Lit>();
}

GnK::~GnK()
{
  vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
  delete real_temp_cl;
}

void GnK::setMaxConflicts(int64_t _max_confl)
{
  max_confl = _max_confl;
}

void GnK::setMaxTime(int64_t _max_time)
{
  max_time = _max_time;
}

bool GnK::addClause(const vec_literals& ps) // Add a clause to the solver.
{
  // Cryptominisat uses a slightly different vec class.
  // Cryptominisat uses a slightly different Lit class too.

  vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
  real_temp_cl.clear();
  for (int i = 0; i < ps.size(); i++)
  {
    real_temp_cl.push_back(CMSat::Lit(var(ps[i]), sign(ps[i])));
  }
  cnf.add_clause(real_temp_cl);

  return true;
}

bool GnK::okay() const // FALSE means solver is in a conflicting state
{
  //return a->okay();
  return true; //TODO AS: implement well
}

void print_log(const mpfr_t& cnt, std::string extra = "") {
    mpfr_t log10_val;
    mpfr_init2(log10_val, 256);
    mpfr_set(log10_val, cnt, MPFR_RNDN);
    if (mpfr_sgn(log10_val) < 0) {
      std::cout << "c s neglog10-estimate" << extra << " ";
      mpfr_neg(log10_val, log10_val, MPFR_RNDN);
    } else {
      std::cout << "c s log10-estimate" << extra << " ";
    }
    mpfr_log10(log10_val, log10_val, MPFR_RNDN);

    char* tmp = nullptr;
    mpfr_asprintf(&tmp, "%.8Re", log10_val);
    std::cout << tmp << std::endl;
    mpfr_free_str(tmp);
    mpfr_clear(log10_val);
}


void print_log(const mpz_class& cnt, std::string extra = "") {
    mpz_class abs_cnt = cnt;
    if (abs_cnt < 0) {
      std::cout << "c s neglog10-estimate" << extra << " ";
      abs_cnt *= -1;
    } else {
      std::cout << "c s log10-estimate" << extra << " ";
    }
    mpfr_t log10_val;
    mpfr_init2(log10_val, 256);
    mpfr_set_z(log10_val, abs_cnt.get_mpz_t(), MPFR_RNDN);
    mpfr_log10(log10_val, log10_val, MPFR_RNDN);

    char* tmp = nullptr;
    mpfr_asprintf(&tmp, "%.8Re", log10_val);
    std::cout << tmp << std::endl;
    mpfr_free_str(tmp);
    mpfr_clear(log10_val);
}

std::string print_mpq_as_scientific(const mpq_class& number) {
    mpf_class mpf_value(number);
    std::ostringstream oss;
    oss << std::scientific << std::setprecision(8) << mpf_value;
    return oss.str();
}

bool GnK::solve(bool& timeout_expired) // Search without assumptions.
{

  /*
   * STP uses -1 for a value of "no timeout" -- this means that we only set the
   * timeout _in the SAT solver_ if the value is >= 0. This avoids us
   * accidentally setting a large limit (or one in the past).
   */

  // CMSat::lbool ret = s->solve(); // TODO AS
  arjun->set_verb(0);
  cnf.set_sampl_vars(sampling_vars_orig);
  std::cout << "c [stp->gnk] Arjun solving instance with " << cnf.nVars()
            << " variables, " << cnf.clauses.size() << " clauses "
            << sampling_vars_orig.size() << " projection vars" << std::endl;
  if (sampling_vars_orig.size() > 0)
    etof_conf.all_indep = false;
  else
    etof_conf.all_indep = false;
  arjun->standalone_minimize_indep(cnf, etof_conf.all_indep);
  // assert(!etof_conf.all_indep);
  if (cnf.get_sampl_vars().size() >= 10) {
    arjun->standalone_elim_to_file(cnf, etof_conf, simp_conf);
  } else cnf.renumber_sampling_vars_for_ganak();

  vector<uint32_t> sampling_vars;
  for (uint32_t i = 0; i < cnf.nVars(); i++)
    sampling_vars.push_back(i);

  std::cout << "c [stp->gnk] GnK solving instance with " << cnf.nVars()
            << " variables, " << cnf.clauses.size() << " clauses "
            << std::endl;

  std::cout << "c [stp->gnk] sampling var size [from arjun] "
          << cnf.get_sampl_vars().size() << ", opt proj var size "
          << cnf.opt_sampl_vars.size() << std::endl;
  // arjun->set_seed(seed);
  // arjun->set_verbosity(0);
  // arjun->set_simp(1);
  // std::cout << "c Arjun SHA revision " << arjun->get_version_info()
  //           << std::endl;

  conf.verb = 0;
  if (seed == 0)
    conf.appmc_timeout = 1;

  Ganak counter(conf, fg);
  counter.new_vars(cnf.nVars());

  std::set<uint32_t> tmp;
  for (auto const& s : cnf.sampl_vars)
    tmp.insert(s + 1);
  counter.set_indep_support(tmp);
  if (cnf.get_opt_sampl_vars_set())
  {
    tmp.clear();
    for (auto const& s : cnf.opt_sampl_vars)
      tmp.insert(s + 1);
    counter.set_optional_indep_support(tmp);
  }
  if (cnf.weighted)
  {
    const uint32_t max_sz =
        std::max(lit_weights.size(), neg_lit_weights.size());
    for (uint32_t i = 0; i < max_sz; ++i)
    {
      double pw = i < lit_weights.size() ? lit_weights[i] : -1.0;
      double nw = i < neg_lit_weights.size() ? neg_lit_weights[i] : -1.0;
      if (pw >= 0.0 || nw >= 0.0)
      {

        // Construct/assign weight objects directly (set_value() not available in
        // current API)
        std::unique_ptr<CMSat::Field> pos;
        std::unique_ptr<CMSat::Field> neg;
        mpq_class pwq(pw);
        mpq_class nwq(nw);

        pos = std::make_unique<ArjunNS::FMpq>(pwq);
        neg = std::make_unique<ArjunNS::FMpq>(nwq);


        counter.set_lit_weight(GanakInt::Lit(i + 1, true), pos);
        counter.set_lit_weight(GanakInt::Lit(i + 1, false), neg);
      }
    }
  }

  // Add clauses
  for (const auto& cl : cnf.clauses)
    counter.add_irred_cl(cms_to_ganak_cl(cl));
  for (const auto& cl : cnf.red_clauses)
    counter.add_red_cl(cms_to_ganak_cl(cl));



  delete arjun;
  std::stringstream ss;
  std::unique_ptr<CMSat::Field> cnt = cnf.multiplier_weight->dup();
  if (!cnf.multiplier_weight->is_zero()) *cnt *= *counter.count();
  ss.setf(std::ios::scientific, std::ios::floatfield);
  ss.precision(40);
  const CMSat::Field* ptr = cnt.get();
  assert(ptr != nullptr);
  // const ArjunNS::FMpz* od = dynamic_cast<const ArjunNS::FMpz*>(ptr);
  // print_log(od->val);
  const ArjunNS::FMpq* od = dynamic_cast<const ArjunNS::FMpq*>(ptr);
  mpfr_t r;
  mpfr_init2(r, 256);
  mpfr_set_q(r, od->val.get_mpq_t(), MPFR_RNDN);
  print_log(r);
  mpfr_clear(r);
  ss << *od;
  std::cout << "c o exact quadruple float "  << print_mpq_as_scientific(od->val) << std::endl;
  std::cout << "c s exact arb frac " << *cnt << std::endl;


  if (counter.get_is_approximate())
    std::cout << "c count its approximate\n";

  // use gmp to get the absolute count of solutions

  std::cout << "s mc " << ss.str() << std::endl;

  exit(0);
  return true;
}

uint8_t GnK::modelValue(uint32_t x) const
{
  //   if (appmc_models[0].size() < sampling_vars.size())
  //     std::cout << "c [stp->appmc] ERROR! found model size is not large enough\n";
  return true;
}

uint32_t GnK::newProjVar(uint32_t x)
{
  sampling_vars_orig.push_back(x);
  return 1;
}

uint32_t GnK::newVar()
{
  cnf.new_var();
  lit_weights.push_back(-1.0);
  neg_lit_weights.push_back(-1.0);
  return cnf.nVars() - 1;
}

void GnK::setVarWeight(uint32_t var, double weight)
{
  if (var >= lit_weights.size())
  {
    lit_weights.resize(var + 1, -1.0);
    neg_lit_weights.resize(var + 1, -1.0);
  }
  lit_weights[var] = weight;
  cnf.weighted = true;
}

void GnK::setNegWeight(uint32_t var, double weight)
{
  if (var >= neg_lit_weights.size())
  {
    neg_lit_weights.resize(var + 1, -1.0);
    lit_weights.resize(var + 1, -1.0);
  }
  neg_lit_weights[var] = weight;
  cnf.weighted = true;
}

void GnK::setVerbosity(int v)
{
  arjun->set_verb(0);
}

unsigned long GnK::nVars() const
{
  return cnf.nVars();
}

void GnK::printStats() const
{
  // s->printStats();
}

void GnK::solveAndDump()
{
  bool t;
  solve(t);
  //s->open_file_and_dump_irred_clauses("clauses.txt");
}

// Count how many literals/bits get fixed subject to the assumptions..
uint32_t
GnK::getFixedCountWithAssumptions(const stp::SATSolver::vec_literals& assumps,
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
