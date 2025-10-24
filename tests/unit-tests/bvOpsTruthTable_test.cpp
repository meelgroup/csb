// New include:
#include "bv3_ops_truth_table.h"


static void assignBit1(stp::SATSolver& solver, unsigned var, bool value) {
  addUnitClause(solver, var, value);
}

// ---------- Subtraction ----------
TEST(BvSubCnfTest, BvSubMatchesTruthTable3Bit) {
  stp::STPMgr mgr;
  stp::SimplifyingNodeFactory snf(*mgr.hashingNodeFactory(), mgr);
  mgr.defaultNodeFactory = &snf;

  stp::SubstitutionMap substitution_map(&mgr);
  stp::Simplifier simplifier(&mgr, &substitution_map);
  stp::ArrayTransformer array_transformer(&mgr, &simplifier);
  stp::ToSATAIG tosat(&mgr, &array_transformer);

  const unsigned W = 3;
  ASTNode x = mgr.CreateSymbol("x_sub", 0, W);
  ASTNode y = mgr.CreateSymbol("y_sub", 0, W);
  ASTNode z = mgr.CreateSymbol("z_sub", 0, W);

  ASTNode diff = mgr.CreateTerm(stp::BVSUB, W, x, y);
  ASTNode eq = mgr.CreateNode(stp::EQ, diff, z);

  Cnf_Dat_t* cnf = tosat.bitblast(eq, false);
  ASSERT_NE(cnf, nullptr);

  const auto& sat_map = tosat.SATVar_to_SymbolIndexMap();
  auto x_it = sat_map.find(x), y_it = sat_map.find(y), z_it = sat_map.find(z);
  ASSERT_TRUE(x_it != sat_map.end() && y_it != sat_map.end() && z_it != sat_map.end());

  const auto& xb = x_it->second; const auto& yb = y_it->second; const auto& zb = z_it->second;
  ASSERT_EQ(xb.size(), W); ASSERT_EQ(yb.size(), W); ASSERT_EQ(zb.size(), W);

  for (const auto& c : BV3_OPS_CASES) {
    stp::SimplifyingMinisat solver;
    tosat.add_cnf_to_solver(solver, cnf);

    assignBits(solver, xb, c.x, W);
    assignBits(solver, yb, c.y, W);
    assignBits(solver, zb, c.sub, W);

    bool tout = false;
    ASSERT_TRUE(solver.solve(tout)) << "x="<<int(c.x)<<" y="<<int(c.y)<<" sub="<<int(c.sub);
    ASSERT_FALSE(tout);
  }

  tosat.release_cnf_memory(cnf);
}

// ---------- Multiplication ----------
TEST(BvMulCnfTest, BvMulMatchesTruthTable3Bit) {
  stp::STPMgr mgr;
  stp::SimplifyingNodeFactory snf(*mgr.hashingNodeFactory(), mgr);
  mgr.defaultNodeFactory = &snf;

  stp::SubstitutionMap substitution_map(&mgr);
  stp::Simplifier simplifier(&mgr, &substitution_map);
  stp::ArrayTransformer array_transformer(&mgr, &simplifier);
  stp::ToSATAIG tosat(&mgr, &array_transformer);

  const unsigned W = 3;
  ASTNode x = mgr.CreateSymbol("x_mul", 0, W);
  ASTNode y = mgr.CreateSymbol("y_mul", 0, W);
  ASTNode z = mgr.CreateSymbol("z_mul", 0, W);

  ASTNode prod = mgr.CreateTerm(stp::BVMULT, W, x, y);
  ASTNode eq = mgr.CreateNode(stp::EQ, prod, z);

  Cnf_Dat_t* cnf = tosat.bitblast(eq, false);
  ASSERT_NE(cnf, nullptr);

  const auto& sat_map = tosat.SATVar_to_SymbolIndexMap();
  auto x_it = sat_map.find(x), y_it = sat_map.find(y), z_it = sat_map.find(z);
  ASSERT_TRUE(x_it != sat_map.end() && y_it != sat_map.end() && z_it != sat_map.end());

  const auto& xb = x_it->second; const auto& yb = y_it->second; const auto& zb = z_it->second;
  ASSERT_EQ(xb.size(), W); ASSERT_EQ(yb.size(), W); ASSERT_EQ(zb.size(), W);

  for (const auto& c : BV3_OPS_CASES) {
    stp::SimplifyingMinisat solver;
    tosat.add_cnf_to_solver(solver, cnf);

    assignBits(solver, xb, c.x, W);
    assignBits(solver, yb, c.y, W);
    assignBits(solver, zb, c.mul, W);

    bool tout = false;
    ASSERT_TRUE(solver.solve(tout)) << "x="<<int(c.x)<<" y="<<int(c.y)<<" mul="<<int(c.mul);
    ASSERT_FALSE(tout);
  }

  tosat.release_cnf_memory(cnf);
}

// ---------- Comparisons ----------

static void checkCmp3Bit(stp::STPMgr& mgr,
                         stp::ArrayTransformer& array_transformer,
                         stp::ToSATAIG& tosat,
                         stp::Kind cmp_kind,
                         const char* tag,
                         bool expected(const BV3OpsCase&)) {
  const unsigned W = 3;
  ASTNode x = mgr.CreateSymbol(std::string("x_")+tag, 0, W);
  ASTNode y = mgr.CreateSymbol(std::string("y_")+tag, 0, W);
  ASTNode t = mgr.CreateSymbol(std::string("t_")+tag, 0, 1);

  ASTNode cond = mgr.CreateNode(cmp_kind, x, y);
  ASTNode one = mgr.CreateBVConst(1, 1);
  ASTNode zero = mgr.CreateBVConst(1, 0);

  ASTNode ite = mgr.CreateTerm(stp::ITE, 1, cond, one, zero);
  ASTNode eq = mgr.CreateNode(stp::EQ, t, ite);

  Cnf_Dat_t* cnf = tosat.bitblast(eq, false);
  ASSERT_NE(cnf, nullptr);

  const auto& sat_map = tosat.SATVar_to_SymbolIndexMap();
  auto x_it = sat_map.find(x), y_it = sat_map.find(y), t_it = sat_map.find(t);
  ASSERT_TRUE(x_it != sat_map.end() && y_it != sat_map.end() && t_it != sat_map.end());
  const auto& xb = x_it->second; const auto& yb = y_it->second; const auto& tb = t_it->second;
  ASSERT_EQ(xb.size(), W); ASSERT_EQ(yb.size(), W); ASSERT_EQ(tb.size(), 1u);

  for (const auto& c : BV3_OPS_CASES) {
    stp::SimplifyingMinisat solver;
    tosat.add_cnf_to_solver(solver, cnf);

    assignBits(solver, xb, c.x, W);
    assignBits(solver, yb, c.y, W);
    assignBit1(solver, tb[0], expected(c));

    bool tout = false;
    ASSERT_TRUE(solver.solve(tout)) << tag << " failed for x="<<int(c.x)<<" y="<<int(c.y);
    ASSERT_FALSE(tout);
  }

  tosat.release_cnf_memory(cnf);
}

TEST(BvCmpCnfTest, UnsignedAndSigned3Bit) {
  stp::STPMgr mgr;
  stp::SimplifyingNodeFactory snf(*mgr.hashingNodeFactory(), mgr);
  mgr.defaultNodeFactory = &snf;
  stp::SubstitutionMap substitution_map(&mgr);
  stp::Simplifier simplifier(&mgr, &substitution_map);
  stp::ArrayTransformer array_transformer(&mgr, &simplifier);
  stp::ToSATAIG tosat(&mgr, &array_transformer);

  auto ULT = [](const BV3OpsCase& c){ return c.ult; };
  auto ULE = [](const BV3OpsCase& c){ return c.ule; };
  auto UGT = [](const BV3OpsCase& c){ return c.ugt; };
  auto UGE = [](const BV3OpsCase& c){ return c.uge; };
  auto SLT = [](const BV3OpsCase& c){ return c.slt; };
  auto SLE = [](const BV3OpsCase& c){ return c.sle; };
  auto SGT = [](const BV3OpsCase& c){ return c.sgt; };
  auto SGE = [](const BV3OpsCase& c){ return c.sge; };

  // Replace enum names with your STP kinds if they differ:
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVLT,  "ult", ULT);
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVLE,  "ule", ULE);
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVGT,  "ugt", UGT);
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVGE,  "uge", UGE);

  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVSLT, "slt", SLT);
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVSLE, "sle", SLE);
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVSGT, "sgt", SGT);
  checkCmp3Bit(mgr, array_transformer, tosat, stp::BVSGE, "sge", SGE);
}
