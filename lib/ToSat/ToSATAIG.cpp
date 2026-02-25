/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
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

#include "stp/ToSat/ToSATAIG.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"

#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unordered_map>
#include <utility>
#include <vector>

namespace stp
{

namespace
{

int aigLiteral(Aig_Obj_t* obj,
               const std::unordered_map<const Aig_Obj_t*, int>& var_ids)
{
  if (obj == nullptr)
    return 0;

  const bool complemented = Aig_IsComplement(obj);
  Aig_Obj_t* regular = Aig_Regular(obj);

  if (Aig_ObjIsConst1(regular))
    return complemented ? 0 : 1;

  const auto it = var_ids.find(regular);
  assert(it != var_ids.end());
  return 2 * it->second + (complemented ? 1 : 0);
}

void printAigAsAiger(Aig_Man_t* aig, std::ostream& out)
{
  std::unordered_map<const Aig_Obj_t*, int> var_ids;

  int next_var = 1;
  for (int i = 0; i < Aig_ManPiNum(aig); ++i)
  {
    Aig_Obj_t* obj = Aig_ManPi(aig, i);
    var_ids[obj] = next_var++;
  }

  std::vector<Aig_Obj_t*> and_nodes;
  for (int i = 0; i < Vec_PtrSize(aig->vObjs); ++i)
  {
    auto* obj = static_cast<Aig_Obj_t*>(Vec_PtrEntry(aig->vObjs, i));
    if (obj == nullptr || !Aig_ObjIsNode(obj))
      continue;

    and_nodes.push_back(obj);
    var_ids[obj] = next_var++;
  }

  const int I = Aig_ManPiNum(aig);
  const int L = 0;
  const int O = Aig_ManPoNum(aig);
  const int A = static_cast<int>(and_nodes.size());
  const int M = I + A;

  out << "aag " << M << " " << I << " " << L << " " << O << " " << A << std::endl;

  for (int pi = 0; pi < Aig_ManPiNum(aig); ++pi)
  {
    Aig_Obj_t* obj = Aig_ManPi(aig, pi);
    out << 2 * var_ids[obj] << std::endl;
  }

  for (int po = 0; po < Aig_ManPoNum(aig); ++po)
  {
    Aig_Obj_t* obj = Aig_ManPo(aig, po);
    int out_lit = aigLiteral(Aig_ObjChild0(obj), var_ids);
    out << out_lit << std::endl;
  }

  for (Aig_Obj_t* and_node : and_nodes)
  {
    const int lhs = 2 * var_ids[and_node];
    int rhs0 = aigLiteral(Aig_ObjChild0(and_node), var_ids);
    int rhs1 = aigLiteral(Aig_ObjChild1(and_node), var_ids);
    if (rhs0 < rhs1)
      std::swap(rhs0, rhs1);

    out << lhs << " " << rhs0 << " " << rhs1 << std::endl;
  }
}

} // namespace

THREAD_LOCAL int ToSATAIG::cnf_calls = 0;

bool ToSATAIG::CallSAT(SATSolver& satSolver, const ASTNode& input,
                       bool needAbsRef)
{
  if (cb != NULL && cb->isUnsatisfiable())
    return false;

  if (!first)
  {
    assert(input == ASTTrue);
    return runSolver(satSolver);
  }

  // Shortcut if known. This avoids calling the setup of the CNF generator.
  // setup of the CNF generator is expensive. NB, these checks have to occur
  // after calling the sat solver (if it's not the first time.)
  if (input == ASTFalse)
    return false;

  if (input == ASTTrue)
    return true;

  first = false;
  Cnf_Dat_t* cnfData = bitblast(input, needAbsRef);
  handle_cnf_options(cnfData, needAbsRef);

  assert(satSolver.nVars() == 0);
  add_cnf_to_solver(satSolver, cnfData);

  if (bm->UserFlags.output_bench_flag)
  {
    cerr << "Converting to CNF via ABC's AIG package can't yet print out bench "
            "format"
         << endl;
  }
  release_cnf_memory(cnfData);

  mark_variables_as_frozen(satSolver);

  return runSolver(satSolver);
}

void ToSATAIG::release_cnf_memory(Cnf_Dat_t* cnfData)
{
  // This releases the memory used by the CNF generator, particularly some data
  // tables.
  // If CNF generation is going to be called lots, we'd rather keep it around.
  // because the datatables are expensive to generate.
  if (cnf_calls == 0)
    Cnf_ClearMemory();

  Cnf_DataFree(cnfData);
  cnf_calls++;
}

void ToSATAIG::handle_cnf_options(Cnf_Dat_t* cnfData, bool needAbsRef)
{
  if (bm->UserFlags.output_CNF_flag)
  {
    std::string fileName;
    if (!bm->UserFlags.cnf_output_file.empty())
    {
      fileName = bm->UserFlags.cnf_output_file;
    }
    else
    {
      std::stringstream fallback;
      fallback << "output_" << bm->CNFFileNameCounter++ << ".cnf";
      fileName = fallback.str();
    }

    const bool is_weighted = (!bm->getWeightSymbols().empty() ||
                              !bm->getNegWeightSymbols().empty());
    Cnf_DataWriteIntoFile(cnfData, const_cast<char*>(fileName.c_str()), 0,
                          is_weighted ? 1 : 0);
    std::cout << "c [stp] bitblasted CNF stored in " << fileName << std::endl;
    std::cout.flush();
    exit(0);
  }

  if (bm->UserFlags.exit_after_CNF)
  {
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();

    if (needAbsRef)
    {
      cerr << "Warning: STP is exiting after generating the first CNF."
           << " But the CNF is probably partial which you probably don't want."
           << " You probably want to disable"
           << " refinement with the \"-r\" command line option." << endl;
    }

    exit(0);
  }
}

Cnf_Dat_t* ToSATAIG::bitblast(const ASTNode& input, bool needAbsRef)
{
  stp::SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);

  BBNodeManagerAIG mgr;
  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(
      &mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags, cb);

  bm->GetRunTimes()->start(RunTimes::BitBlasting);
  BBNodeAIG BBFormula = bb.BBForm(input);
  bm->GetRunTimes()->stop(RunTimes::BitBlasting);

  delete cb;
  cb = NULL;
  bb.cb = NULL;

  bm->GetRunTimes()->start(RunTimes::CNFConversion);
  Cnf_Dat_t* cnfData = NULL;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, needAbsRef, mgr);
  bm->GetRunTimes()->stop(RunTimes::CNFConversion);

  if (bm->UserFlags.output_AIG_flag)
  {
    std::string fileName;
    if (!bm->UserFlags.aig_output_file.empty())
    {
      fileName = bm->UserFlags.aig_output_file;
    }
    else
    {
      std::stringstream fallback;
      fallback << "output_" << bm->CNFFileNameCounter++ << ".aag";
      fileName = fallback.str();
    }

    std::ofstream aigOut(fileName);
    if (!aigOut)
    {
      cerr << "Cannot open output file for AIG dump: " << fileName << endl;
      std::exit(-1);
    }

    printAigAsAiger(mgr.aigMgr, aigOut);
    aigOut.close();
    std::cout << "c [stp] bitblasted AIG stored in " << fileName << std::endl;
    std::cout.flush();
    std::exit(0);
  }

  // Free the memory in the AIGs.
  BBFormula = BBNodeAIG(); // null node
  mgr.stop();

  return cnfData;
}

void ToSATAIG::add_cnf_to_solver(SATSolver& satSolver, Cnf_Dat_t* cnfData)
{
  bm->GetRunTimes()->start(RunTimes::SendingToSAT);

  // Create a new sat variable for each of the variables in the CNF.
  int satV = satSolver.nVars();
  for (int i = 0; i < cnfData->nVars - satV; i++)
  {
    satSolver.newVar();
    if (cnfData->lProjVars[i] == 1)
    {
      satSolver.newProjVar(i);
    }
  }

  for (const auto& ws : bm->getWeightSymbols())
  {
    auto it = nodeToSATVar.find(ws.first);
    if (it == nodeToSATVar.end())
      continue;
    const std::vector<unsigned>& vars = it->second;
    if (vars.size() != 1)
      continue;
    unsigned var = vars[0];
    if (var != ~((unsigned)0)){
      satSolver.setVarWeight(var, ws.second);
      cnfData->lit_weights[var] = ws.second;
    }
  }

  for (const auto& ws : bm->getNegWeightSymbols())
  {
    auto it = nodeToSATVar.find(ws.first);
    if (it == nodeToSATVar.end())
      continue;
    const std::vector<unsigned>& vars = it->second;
    if (vars.size() != 1)
      continue;
    unsigned var = vars[0];
    if (var != ~((unsigned)0)){
      satSolver.setNegWeight(var, ws.second);
      cnfData->neg_lit_weights[var] = ws.second;
    }
  }

  SATSolver::vec_literals satSolverClause;
  for (int i = 0; i < cnfData->nClauses; i++)
  {
    satSolverClause.clear();
    for (int *pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i + 1];
         pLit < pStop; pLit++)
    {
      uint32_t var = (*pLit) >> 1;
      assert((var < satSolver.nVars()));
      Minisat::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
      satSolverClause.push(l);
    }

    satSolver.addClause(satSolverClause);
    if (!satSolver.okay())
      break;
  }
  bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
}

void ToSATAIG::mark_variables_as_frozen(SATSolver& satSolver)
{
  for (ArrayTransformer::ArrType::iterator it =
           arrayTransformer->arrayToIndexToRead.begin();
       it != arrayTransformer->arrayToIndexToRead.end(); it++)
  {
    const ArrayTransformer::arrTypeMap& atm = it->second;

    for (ArrayTransformer::arrTypeMap::const_iterator arr_it = atm.begin();
         arr_it != atm.end(); arr_it++)
    {
      const ArrayTransformer::ArrayRead& ar = arr_it->second;
      ASTNodeToSATVar::iterator it = nodeToSATVar.find(ar.index_symbol);
      if (it != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          satSolver.setFrozen(v[i]);
      }

      ASTNodeToSATVar::iterator it2 = nodeToSATVar.find(ar.symbol);
      if (it2 != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it2->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          satSolver.setFrozen(v[i]);
      }
    }
  }
}

bool ToSATAIG::runSolver(SATSolver& satSolver)
{
  bm->GetRunTimes()->start(RunTimes::Solving);
  bool result = satSolver.solve(bm->soft_timeout_expired);
  bm->GetRunTimes()->stop(RunTimes::Solving);

  if (bm->UserFlags.stats_flag)
    satSolver.printStats();

  return result;
}

ToSATAIG::~ToSATAIG()
{
  ClearAllTables();
}
} // namespace stp
