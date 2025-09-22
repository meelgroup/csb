/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Andrew V. Jones
 *
 * BEGIN DATE: November, 2005
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

#include "main_common.h"

#include <boost/program_options.hpp>
#include <new>
namespace po = boost::program_options;

using namespace stp;
using std::cerr;
using std::cout;
using std::endl;

/********************************************************************
 * MAIN FUNCTION:
 *
 * step 0. Parse the input into an ASTVec.
 * step 1. Do BV Rewrites
 * step 2. Bitblasts the ASTNode.
 * step 3. Convert to CNF
 * step 4. Convert to SAT
 * step 5. Call SAT to determine if input is SAT or UNSAT
********************************************************************/

class ExtraMain : public Main
{
public:
  void try_parsing_options(int argc, char** argv, po::variables_map& vm,
                           po::positional_options_description& pos_options);
  int create_and_parse_options(int argc, char** argv);
  void create_options();
  int parse_options(int argc, char** argv);

  po::options_description cmdline_options;
  po::options_description visible_options;
  po::positional_options_description pos_options;
};

int ExtraMain::create_and_parse_options(int argc, char** argv)
{
  create_options();
  int ret = parse_options(argc, argv);
  if (ret != 0)
  {
    return ret;
  }
  return 0;
}

void ExtraMain::try_parsing_options(
    int argc, char** argv, po::variables_map& vm,
    po::positional_options_description& pos_options)
{
  try
  {
    po::store(po::command_line_parser(argc, argv)
                  .options(cmdline_options)
                  .positional(pos_options)
                  .run(),
              vm);

    if (vm.count("help"))
    {
      cout << "USAGE: csb [mode] <input-file>" << endl
           << " where input is SMTLIB2 file" << endl;

      cout << visible_options << '\n';
      cout << "weights are supported only in ganak (default) mode." << endl;
      exit(0);
    }

    po::notify(vm);
  }
  catch (boost::exception_detail::clone_impl<
         boost::exception_detail::error_info_injector<po::unknown_option>>& c)
  {
    cout << "Some option you gave was wrong. Please give '--help' to get help"
         << endl;
    cout << "Unknown option: " << c.what() << endl;
    exit(-1);
  }
  catch (boost::bad_any_cast& e)
  {
    std::cerr << "ERROR! You probably gave a wrong argument type (Bad cast): "
              << e.what() << endl;

    exit(-1);
  }
  catch (boost::exception_detail::clone_impl<
         boost::exception_detail::error_info_injector<
             po::invalid_option_value>>& what)
  {
    cerr << "Invalid value '" << what.what() << "'"
         << " given to option '" << what.get_option_name() << "'" << endl;

    exit(-1);
  }
  catch (boost::exception_detail::clone_impl<
         boost::exception_detail::error_info_injector<
             po::multiple_occurrences>>& what)
  {
    cerr << "Error: " << what.what() << " of option '" << what.get_option_name()
         << "'" << endl;

    exit(-1);
  }
  catch (boost::exception_detail::clone_impl<
         boost::exception_detail::error_info_injector<po::required_option>>&
             what)
  {
    cerr << "You forgot to give a required option '" << what.get_option_name()
         << "'" << endl;

    exit(-1);
  }
}

void ExtraMain::create_options()
{
  po::options_description hiddenOptions("Hidden options");
  hiddenOptions.add_options()("file", po::value<string>(&infile), "input file");

  // Declare the supported options.
  po::options_description general_options("Most important options");
  general_options.add_options()("help,h", "print this help")(
      "version", "print version number");

#define BOOL_ARG(b0) po::value<bool>(&(b0))->default_value(b0)
#define INT64_ARG(i0) po::value<int64_t>(&(i0))->default_value(i0)

  po::options_description simplification_options("Simplifications");
  simplification_options.add_options()("disable-simplifications",
                                       "disable all simplifications")(
      "switch-word,w", "switch off wordlevel solver")(
      "disable-opt-inc", "disable rewriting simplifier")(
      "disable-cbitp", "disable constant bit propagation")(
      "disable-equality", "disable equality propagation")(
      "size-reducing-only", "size reducing simplifications only")

      ("unconstrained-variable-elimination",
       BOOL_ARG(bm->UserFlags.enable_unconstrained),
       "Unconstrained variables are eliminated.")

          ("aig-rewrite-passes",
           INT64_ARG(bm->UserFlags.AIG_rewrites_iterations),
           "Iterations of AIG rewriting to perform")

              ("flattening", BOOL_ARG(bm->UserFlags.enable_flatten),
               "Enable sharing-aware flattening of >2 arity nodes")

                  ("rewriting",
                   BOOL_ARG(bm->UserFlags.enable_sharing_aware_rewriting),
                   "Enable sharing-aware rewriting")

                      ("split-extracts",
                       BOOL_ARG(bm->UserFlags.enable_split_extracts),
                       "Create new variables for some extracts")

                          ("ite-context-simplifications",
                           BOOL_ARG(bm->UserFlags.enable_ite_context),
                           "Use what is known to be true in an if-then-else "
                           "node to simplify the true or false branches")

                              ("aig-core-simplification",
                               BOOL_ARG(bm->UserFlags.enable_aig_core_simplify),
                               "Simplify the propositional core with AIGs")

                                  ("use-intervals",
                                   BOOL_ARG(bm->UserFlags.enable_use_intervals),
                                   "Simplify with interval analysis")

                                      ("pure-literals",
                                       BOOL_ARG(
                                           bm->UserFlags.enable_pure_literals),
                                       "Pure literals are replaced.")

                                          ("always-true",
                                           BOOL_ARG(bm->UserFlags
                                                        .enable_always_true),
                                           "Nodes that are always true (e.g. "
                                           "asserted) are replaced through out "
                                           "the problem by true")

                                              ("merge-same",
                                               BOOL_ARG(bm->UserFlags
                                                            .enable_merge_same),
                                               "Uses simple boolean algebra "
                                               "rules to combine conjuncts at "
                                               "the top level")

                                                  ("bit-blast-simplification",
                                                   INT64_ARG(
                                                       bm->UserFlags
                                                           .bitblast_simplification),
                                                   "Part-way through "
                                                   "simplifying, convert to "
                                                   "AIGs and look for bits "
                                                   "that the AIGs figure out "
                                                   "are true/false or the same "
                                                   "as another node. If the "
                                                   "difficulty is less than "
                                                   "this number. -1 means "
                                                   "always.")(
                                                      "size-reducing-fixed-"
                                                      "point-limit",
                                                      INT64_ARG(
                                                          bm->UserFlags
                                                              .size_reducing_fixed_point),
                                                      "If the number of "
                                                      "non-leaf nodes is fewer "
                                                      "than this number, run "
                                                      "size-reducing "
                                                      "simplifications to a "
                                                      "fixed-point. -1 means "
                                                      "always.")

                                                      ("simplify-to-constants-"
                                                       "only,simply_to_"
                                                       "constants_only",
                                                       BOOL_ARG(
                                                           bm->UserFlags
                                                               .simplify_to_constants_only),
                                                       "Use just the "
                                                       "simplifications from "
                                                       "the potentially size "
                                                       "increasing suite that "
                                                       "transform nodes to "
                                                       "constants")

                                                          ("difficulty-"
                                                           "reversion,"
                                                           "difficulty_"
                                                           "reversion",
                                                           BOOL_ARG(
                                                               bm->UserFlags
                                                                   .difficulty_reversion),
                                                           "Undo size "
                                                           "increasing "
                                                           "simplifications if "
                                                           "they haven't made "
                                                           "the problem "
                                                           "simpler");

  po::options_description solver_options("SAT Solver options");
  solver_options.add_options()
#ifdef USE_CRYPTOMINISAT
      ("cryptominisat",
       "use cryptominisat as the solver. Only use CryptoMiniSat 5.0 or above "
       "(default).")("threads",
                     po::value<int>(&bm->UserFlags.num_solver_threads)
                         ->default_value(bm->UserFlags.num_solver_threads),
                     "Number of threads for cryptominisat")
#endif
#ifdef USE_RISS
          ("riss", "use Riss as the solver"
#ifndef USE_CRYPTOMINISAT
                   "(default)."
#endif
           )
#endif
              ("simplifying-minisat",
               "use installed simplifying minisat version as the solver")(
                  "minisat", "use installed minisat version as the solver "
#ifndef USE_CRYPTOMINISAT
#ifndef USE_RISS
                             "(default)"
#endif
#endif
                  );
#ifdef USE_UNIGEN
  solver_options.add_options()
      ("unisamp,u", "use unisamp as solver -- behave as a "
                     "almost-uniform sampler")(
      "cmsgen,s",
      "use cmsgen as solver -- behave as a uniform like sampler")(
      "approxmc,a",
      "use approxmc as solver -- behave as a approximate counter");
#endif
#ifdef USE_GANAK
  solver_options.add_options()("ganak,e",
                               "use ganak as solver -- behave as a exact counter");
#endif
  solver_options.add_options()
      ("seed",
       po::value<uint64_t>(&bm->UserFlags.unisamp_seed)
           ->default_value(bm->UserFlags.unisamp_seed),
       "Seed for counting and sampling")(
      "num-samples,n",
      po::value<uint64_t>(&bm->UserFlags.num_samples)
          ->default_value(bm->UserFlags.num_samples),
      "Number of samples to generate in sampling mode");

  po::options_description refinement_options("Refinement options");
  refinement_options.add_options()(
      "ackermanize,r", po::bool_switch(&(bm->UserFlags.ackermannisation)),
      "eagerly encode array-read axioms (Ackermannistaion)");

  po::options_description print_options("Printing options");
  print_options.add_options()(
      "print-stpinput,b",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_flag)),
      "print STP input back to cout")(
      "print-back-CVC",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_CVC_flag)),
      "print input in CVC format, then exit")(
      "print-back-SMTLIB2",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_SMTLIB2_flag)),
      "print input in SMT-LIB2 format, then exit")(
      "print-back-SMTLIB1",
      po::bool_switch((&bm->UserFlags.print_STPinput_back_SMTLIB1_flag)),
      "print input in SMT-LIB1 format, then exit")(
      "print-back-GDL",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_GDL_flag)),
      "print AiSee's graph format, then exit")(
      "print-back-dot",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_dot_flag)),
      "print dotty/neato's graph format, then exit")(
      "print-counterex,p",
      po::bool_switch(&(bm->UserFlags.print_counterexample_flag)),
      "print counterexample")(
      "print-counterexbin,y",
      po::bool_switch(&(bm->UserFlags.print_binary_flag)),
      "print counterexample in binary")(
      "print-arrayval,q",
      po::bool_switch(&(bm->UserFlags.print_arrayval_declaredorder_flag)),
      "print arrayval declared order")(
      "print-functionstat", po::bool_switch(&(bm->UserFlags.stats_flag)),
      "print function statistics")(
      "print-quickstat,t",
      po::bool_switch(&(bm->UserFlags.quick_statistics_flag)),
      "print quick statistics")(
      "print-nodes,v", po::bool_switch(&(bm->UserFlags.print_nodes_flag)),
      "print nodes ")("print-output",
                      po::bool_switch(&(bm->UserFlags.print_output_flag)),
                      "Print output");

  po::options_description input_options("Input options");
  input_options.add_options()("SMTLIB1,m", "use the SMT-LIB1 format parser")(
      "SMTLIB2", "use the SMT-LIB2 format parser")("CVC",
                                                   "use the CVC format parser");

  po::options_description output_options("Output options");
  output_options.add_options()(
      "cnf,c", po::bool_switch(&(bm->UserFlags.output_CNF_flag)),
      "get model preserving bitblasted CNF")(
      "output-bench", po::bool_switch(&(bm->UserFlags.output_bench_flag)),
      "save in ABC's bench format to output.bench");


  po::options_description bb_options("Bit-blasting options");
  bb_options.add_options()
    ("bb.div-v1",
      BOOL_ARG(bm->UserFlags.division_variant_1),
      "unsigned division encoding variant 1")

    ("bb.div-v2",
      BOOL_ARG(bm->UserFlags.division_variant_2),
      "unsigned division encoding variant 2")

    ("bb.div-v3",
      BOOL_ARG(bm->UserFlags.division_variant_3),
      "unsigned division encoding variant 3")

    ("bb.add-v1",
      BOOL_ARG(bm->UserFlags.adder_variant),
      "addition encoding variant 1")

    ("bb.add-v2",
      BOOL_ARG(bm->UserFlags.bvplus_variant),
      "addition encoding variant 2")

    ("bb.vle-v1",
      BOOL_ARG(bm->UserFlags.bbbvle_variant),
      "comparison encoding variant 1")

    ("bb.mult-variant",
     INT64_ARG(bm->UserFlags.multiplication_variant),
    "unsigned multiplication variant")

    ("bb.mult-v2",
      BOOL_ARG(bm->UserFlags.upper_multiplication_bound),
      "unsigned multiplication variant 2")

    ("bb.conjoin-constant",
      BOOL_ARG(bm->UserFlags.conjoin_to_top),
      "When constant-bit propagation detects a constant bit during AIG construction, assert the AIG node and replace it, in the AIG, by the constant bit"
      );


  po::options_description misc_options("Output options");
  misc_options.add_options()("exit-after-CNF",
                             po::bool_switch(&(bm->UserFlags.exit_after_CNF)),
                             "exit after the CNF has been generated")

      ("max-num-confl,max_num_confl,g",
       INT64_ARG(bm->UserFlags.timeout_max_conflicts),
       "Number of conflicts after which the SAT solver gives up. "
       "-1 means never")

          ("max-time,max_time,k", INT64_ARG(bm->UserFlags.timeout_max_time),
           "Number of seconds after which the SAT solver gives up. "
           "-1 means never.")

              ("verb-count,x",
               po::bool_switch(&(bm->UserFlags.verbose_in_counting)),
               "Be verbose in counting/sampling mode")

                  ("check-sanity,d",
                   po::bool_switch(&(bm->UserFlags.check_counterexample_flag)),
                   "construct counterexample and check it");

#undef BOOL_ARG
#undef INT64_ARG

  cmdline_options.add(general_options)
      .add(simplification_options)
      .add(solver_options)
      .add(refinement_options)
      .add(bb_options)
      .add(print_options)
      .add(input_options)
      .add(output_options)
      .add(misc_options)
      .add(hiddenOptions);

  new (&visible_options) po::options_description("Most important options");
  visible_options.add_options()("help,h", "print this help")
#ifdef USE_UNIGEN
      ("unisamp,u", "almost-uniform sampler mode (unigen backend)")
      ("cmsgen,s", "uniform like sampler (cmsgen backend)")
      ("approxmc,a", "approximate counting mode (approxmc backend)")
#endif
#ifdef USE_GANAK
      ("ganak,e", "exact counting mode (ganak backend) [default]")
#endif
      ("seed", po::value<uint64_t>()->default_value(bm->UserFlags.unisamp_seed),
      "Seed for counting and sampling")(
      "num-samples,n",
       po::value<uint64_t>()->default_value(bm->UserFlags.num_samples),
       "Number of samples to generate in sampling mode");

  pos_options.add("file", 1);
}

int ExtraMain::parse_options(int argc, char** argv)
{
  po::variables_map vm;
  try_parsing_options(argc, argv, vm, pos_options);
  onePrintBack = bm->UserFlags.get_print_output_at_all();

  if (vm.count("disable-opt-inc"))
  {
    bm->UserFlags.optimize_flag = false;
  }

  if (vm.count("switch-word"))
  {
    bm->UserFlags.wordlevel_solve_flag = false;
  }

  if (vm.count("disable-cbitp"))
  {
    bm->UserFlags.bitConstantProp_flag = false;
  }

  int selected_type = 0;
  if (vm.count("CVC"))
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (vm.count("SMTLIB2"))
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  if (vm.count("SMTLIB1"))
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = true;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (selected_type > 1)
  {
    cout << "ERROR: You have selected more than one parsing option from"
            "CVC/SMTLIB1/SMTLIB2"
         << endl;
    std::exit(-1);
  }

  if (selected_type == 0)
  {
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  if (vm.count("simplifying-minisat"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
  }

  if (vm.count("minisat"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
  }

#ifdef USE_CRYPTOMINISAT
  if (vm.count("cryptominisat"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CRYPTOMINISAT5_SOLVER;
    std::cout << "CryptoMiniSat5 solver selected" << std::endl;
  }
#endif

#ifdef USE_GANAK
  if (vm.count("ganak"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::GANAK_SOLVER;
    bm->UserFlags.counting_mode = true;
  }
#endif

#ifndef USE_GANAK
  if (vm.count("ganak"))
  {
    cout << "ERROR: Ganak support was not enabled at configure time." << endl;
    std::exit(-1);
  }
#endif
#ifdef USE_UNIGEN
  if (vm.count("unisamp"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::UNIGEN_SOLVER;
    bm->UserFlags.sampling_mode = true;
    bm->UserFlags.almost_uniform_sampling = true;
  }
  if (vm.count("cmsgen"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CMSGEN_SOLVER;
    bm->UserFlags.sampling_mode = true;
    bm->UserFlags.uniform_like_sampling = true;
  }
  if (vm.count("approxmc"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::APPROXMC_SOLVER;
    bm->UserFlags.counting_mode = true;
  }

  if (bm->UserFlags.sampling_mode && bm->UserFlags.counting_mode)
  {
    cout << "ERROR: You have selected both sampling and counting mode" << endl;
    std::exit(-1);
  }
#else
  if (vm.count("unisamp") || vm.count("cmsgen") || vm.count("approxmc"))
  {
    cout << "ERROR: This build does not include UniGen/ApproxMC/CMSGen support."
         << endl;
    cout << "Reconfigure the project with UniGen enabled to use these options."
         << endl;
    std::exit(-1);
  }
#endif
#ifdef USE_GANAK
  if (bm->UserFlags.solver_to_use == UserDefinedFlags::GANAK_SOLVER &&
      !bm->UserFlags.sampling_mode && !bm->UserFlags.counting_mode)
  {
    bm->UserFlags.counting_mode = true;
  }
#endif
#ifdef USE_GANAK

  if (bm->UserFlags.sampling_mode || bm->UserFlags.counting_mode)
  {
    // disable all simplifications while counting or sampling
    bm->UserFlags.bitConstantProp_flag = false;
    bm->UserFlags.optimize_flag = false;
    bm->UserFlags.disableSimplifications();
    bm->UserFlags.propagate_equalities = false;
  }
#endif

  if (vm.count("disable-simplifications"))
  {
    bm->UserFlags.disableSimplifications();
  }

  if (vm.count("size-reducing-only"))
  {
    bm->UserFlags.disableSizeIncreasingSimplifications();
  }

  if (vm.count("disable-equality"))
  {
    bm->UserFlags.propagate_equalities = false;
  }

  const char* backend_name = nullptr;
  switch (bm->UserFlags.solver_to_use)
  {
    case UserDefinedFlags::GANAK_SOLVER:
      backend_name = "ganak";
      break;
    case UserDefinedFlags::APPROXMC_SOLVER:
      backend_name = "approxmc";
      break;
    case UserDefinedFlags::UNIGEN_SOLVER:
      backend_name = "unigen";
      break;
    case UserDefinedFlags::CMSGEN_SOLVER:
      backend_name = "cmsgen";
      break;
    default:
      break;
  }

  if (backend_name != nullptr)
  {
    cout << "c [stp] using " << backend_name << " backend" << endl;
  }

  if (selected_type == 0)
  {
    // No parser is explicity requested.
    check_infile_type();
  }

  if (vm.count("version"))
  {
    printVersionInfo();
    exit(0);
  }

  return 0;
}

int main(int argc, char** argv)
{
  ExtraMain main;
  return main.main(argc, argv);
}
