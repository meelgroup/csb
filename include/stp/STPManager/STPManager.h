/********************************************************************
 * AUTHORS: Vijay Ganesh
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

#ifndef STPMGR_H
#define STPMGR_H

#include "stp/AST/ASTBVConst.h"
#include "stp/AST/ASTInterior.h"
#include "stp/AST/ASTNode.h"
#include "stp/AST/ASTSymbol.h"

#include "stp/AST/AST.h"
#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Util/Attributes.h"

namespace stp
{
/*
 * STP Node Manager. Tools for managing AST nodes.
 */
class STPMgr
{
  friend class ASTNode;
  friend class ASTInterior;
  friend class ASTBVConst;
  friend class ASTSymbol;
  friend ASTNode HashingNodeFactory::CreateNode(const Kind kind,
                                                const ASTVec& back_children);

private:
  // Typedef for unique Interior node table.
  typedef std::unordered_set<ASTInterior*, ASTInterior::ASTInteriorHasher,
                             ASTInterior::ASTInteriorEqual>
      ASTInteriorSet;

  // Typedef for unique Symbol node (leaf) table.
  typedef std::unordered_set<ASTSymbol*, ASTSymbol::ASTSymbolHasher,
                             ASTSymbol::ASTSymbolEqual>
      ASTSymbolSet;

  // Typedef for unique BVConst node (leaf) table.
  typedef std::unordered_set<ASTBVConst*, ASTBVConst::ASTBVConstHasher,
                             ASTBVConst::ASTBVConstEqual>
      ASTBVConstSet;

  // Unique node tables that enables common subexpression sharing
  ASTInteriorSet _interior_unique_table;

  // Table for variable names, let names etc.
  ASTSymbolSet _symbol_unique_table;

  ASTNodeSet _proj_symbol_list;

  // Table to uniquefy bvconst
  ASTBVConstSet _bvconst_unique_table;

  uint8_t last_iteration;

public:
  HashingNodeFactory* hashingNodeFactory;
  NodeFactory* defaultNodeFactory;

  // frequently used nodes
  ASTNode ASTFalse, ASTTrue, ASTUndefined;

  bool soft_timeout_expired;

  // No nodes should already have the iteration number that is returned from
  // here. This never returns zero.
  uint8_t getNextIteration()
  {
    if (last_iteration == 255)
    {
      resetIteration();
      last_iteration = 0;
    }

    uint8_t result = ++last_iteration;
    assert(result != 0);
    return result;
  }

  // Detauls the iteration count back to zero.
  void resetIteration()
  {
    for (ASTInteriorSet::iterator it = _interior_unique_table.begin();
         it != _interior_unique_table.end(); it++)
    {
      (*it)->iteration = 0;
    }

    for (ASTSymbolSet::iterator it = _symbol_unique_table.begin();
         it != _symbol_unique_table.end(); it++)
    {
      (*it)->iteration = 0;
    }

    for (ASTBVConstSet::iterator it = _bvconst_unique_table.begin();
         it != _bvconst_unique_table.end(); it++)
    {
      (*it)->iteration = 0;
    }
  }

  size_t getAssertLevel() { return _asserts.size(); }

private:
  // Stack of Logical Context. each entry in the stack is a logical
  // context. A logical context is a vector of assertions. The
  // logical context is represented by a ptr to a vector of
  // assertions in that logical context. Logical contexts are
  // created by PUSH/POP
  vector<ASTVec*> _asserts;

  // Memo table that tracks terms already seen
  ASTNodeMap TermsAlreadySeenMap;

  // The query for the current logical context. BUG probably wrongly handled
  // and gets mixed up with the state, which it shouldn't (otherwise, next
  // query will be affected)
  ASTNode _current_query;

  // Ptr to class that reports on the running time of various parts
  // of the code
  RunTimes* runTimes;

  /****************************************************************
   * Private Member Functions                                     *
   ****************************************************************/

  // Destructively appends back_child nodes to front_child nodes.
  // If back_child nodes is NULL, no appending is done.  back_child
  // nodes are not modified.  Then it returns the hashed copy of the
  // node, which is created if necessary.
  ASTInterior* CreateInteriorNode(Kind kind, ASTInterior* new_node,
                                  const ASTVec& back_children = _empty_ASTVec);

  // Create unique ASTInterior node.
  ASTInterior* LookupOrCreateInterior(ASTInterior* n);

  // Create unique ASTSymbol node.
  ASTSymbol* LookupOrCreateSymbol(ASTSymbol& s);

  // Called whenever we want to make sure that the Symbol is
  // declared during semantic analysis
  bool LookupSymbol(ASTSymbol& s);

  // Called by ASTNode constructors to uniqueify ASTBVConst
  ASTBVConst* LookupOrCreateBVConst(ASTBVConst& s);

  // Cache of zero/one/max BVConsts of different widths.
  ASTVec zeroes;
  ASTVec ones;
  ASTVec max;

  // Set of new symbols introduced that replace the array read terms
  ASTNodeSet Introduced_SymbolsSet;

  CBV CreateBVConstVal;

public:
  bool LookupSymbol(const char* const name);
  bool LookupSymbol(const char* const name, ASTNode& output);

  /****************************************************************
   * Public Flags                                                 *
   ****************************************************************/
  UserDefinedFlags UserFlags;

  // This flag indicates as to whether the input has been determined
  // to be valid or not by this tool
  bool ValidFlag;

  // count is used in the creation of new variables
  unsigned int _symbol_count;

  // The value to append to the filename when saving the CNF.
  unsigned int CNFFileNameCounter;

  /****************************************************************
   * Public Member Functions                                      *
   ****************************************************************/

  DLL_PUBLIC STPMgr()
      : last_iteration(0), soft_timeout_expired(false), _symbol_count(0),
        CNFFileNameCounter(0)
  {
    ValidFlag = false;

    // Need to initiate the node factories before any nodes are created.
    hashingNodeFactory = new HashingNodeFactory(*this);
    defaultNodeFactory = hashingNodeFactory;

    ASTFalse = CreateNode(FALSE);
    ASTTrue = CreateNode(TRUE);
    ASTUndefined = CreateNode(UNDEFINED);
    runTimes = new RunTimes();
    _current_query = ASTUndefined;
    CreateBVConstVal = NULL;
  }

  RunTimes* GetRunTimes(void) { return runTimes; }

  unsigned int NodeSize(const ASTNode& a);

  /****************************************************************
   * Create Symbol and BVConst functions                          *
   ****************************************************************/

  // Create and return an ASTNode for a symbol
  ASTNode LookupOrCreateSymbol(const char* const name);

  // Create and return an ASTNode for a symbol Width is number of bits.
  ASTNode CreateOneConst(unsigned int width);
  ASTNode CreateTwoConst(unsigned int width);
  ASTNode CreateMaxConst(unsigned int width);
  ASTNode CreateZeroConst(unsigned int width);
  DLL_PUBLIC ASTNode CreateBVConst(CBV bv, unsigned width);
  ASTNode CreateBVConst(const char* strval, int base);
  ASTNode CreateBVConst(std::string strval, int base, int bit_width);
  ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst);
  ASTNode charToASTNode(unsigned char* strval, int base, int bit_width);

  /****************************************************************
   * Create Node functions                                        *
   ****************************************************************/

  DLL_PUBLIC inline ASTNode
  CreateSymbol(const char* const name, unsigned indexWidth, unsigned valueWidth)
  {
    return defaultNodeFactory->CreateSymbol(name, indexWidth, valueWidth);
  }

  // Create and return an interior ASTNode
  DLL_PUBLIC inline ASTNode CreateNode(stp::Kind kind,
                                       const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, children);
  }

  DLL_PUBLIC inline ASTNode
  CreateNode(Kind kind, const ASTNode& child0,
             const ASTVec& back_children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, child0, back_children);
  }

  DLL_PUBLIC inline ASTNode
  CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
             const ASTVec& back_children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, child0, child1, back_children);
  }

  DLL_PUBLIC inline ASTNode
  CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
             const ASTNode& child2, const ASTVec& back_children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, child0, child1, child2,
                                          back_children);
  }

  /****************************************************************
   * Create Term functions                                        *
   ****************************************************************/

  // Create and return an ASTNode for a term
  inline ASTNode CreateTerm(stp::Kind kind, unsigned int width,
                            const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, children);
  }

  inline ASTNode CreateArrayTerm(stp::Kind kind, unsigned int indexWidth,
                                 unsigned int width,
                                 const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateArrayTerm(kind, indexWidth, width,
                                               children);
  }

  inline ASTNode CreateTerm(Kind kind, unsigned int width,
                            const ASTNode& child0,
                            const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, child0, children);
  }

  inline ASTNode CreateTerm(Kind kind, unsigned int width,
                            const ASTNode& child0, const ASTNode& child1,
                            const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, child0, child1,
                                          children);
  }

  inline ASTNode CreateTerm(Kind kind, unsigned int width,
                            const ASTNode& child0, const ASTNode& child1,
                            const ASTNode& child2,
                            const ASTVec& /*children*/ = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, child0, child1, child2);
  }

  /****************************************************************
   * Functions that manage logical context                        *
   ****************************************************************/

  void Pop(void);
  void Push(void);

  // Queries aren't maintained on a stack.
  // Used by CVC & C-interface.
  const ASTNode GetQuery();
  void SetQuery(const ASTNode& q);

  const ASTVec GetAsserts();
  const ASTVec getVectorOfAsserts();

  // add a query/assertion to the current logical context
  void AddAssert(const ASTNode& assert);

  /****************************************************************
   * Toplevel printing and stats functions                        *
   ****************************************************************/

  // For printing purposes
  // Used just by the CVC parser.
  ASTVec ListOfDeclaredVars;

  // For printing purposes
  // Used just via the C-interface.
  // Note, not maintained properly wrt push/pops
  vector<stp::ASTNode> decls;

  // Nodes seen so far
  ASTNodeSet PLPrintNodeSet;

  // Map from ASTNodes to LetVars
  ASTNodeMap NodeLetVarMap;

  // This is a vector which stores the Node to LetVars pairs. It
  // allows for sorted printing, as opposed to NodeLetVarMap
  vector<std::pair<ASTNode, ASTNode>> NodeLetVarVec;

  // A partial Map from ASTNodes to LetVars. Needed in order to
  // correctly print shared subterms inside the LET itself
  ASTNodeMap NodeLetVarMap1;

  // prints statistics for the ASTNode.
  void ASTNodeStats(const char* c, const ASTNode& a);

  // Print variable to the input stream
  void printVarDeclsToStream(ostream& os, ASTNodeSet& symbols);

  // Print assertions to the input stream
  void printAssertsToStream(ostream& os);

  // Variables are added automatically to the introduced_symbolset. Variables
  // in the set aren't printed out as part of the counter example.
  ASTNode CreateFreshVariable(int indexWidth, int valueWidth,
                              std::string prefix)
  {
    char* d = (char*)alloca(sizeof(char) * (32 + prefix.length()));
    sprintf(d, "%s_%d", prefix.c_str(), _symbol_count++);
    assert(!LookupSymbol(d));

    ASTNode CurrentSymbol = CreateSymbol(d, indexWidth, valueWidth);
    Introduced_SymbolsSet.insert(CurrentSymbol);
    return CurrentSymbol;
  }

  bool addProjSymbol(ASTNode& s)
  {
    _proj_symbol_list.insert(s);
    return true;
  }

  bool isProjSymbol(ASTNode& s)
  {
    if (_proj_symbol_list.size() == 0)
      return true;
    return _proj_symbol_list.find(s) != _proj_symbol_list.end();
  }

  bool isAnyProjSymbolDeclared()
  {
    if (_proj_symbol_list.size() == 0)
      return false;
    return true;
  }

  bool FoundIntroducedSymbolSet(const ASTNode& in)
  {
    if (Introduced_SymbolsSet.find(in) != Introduced_SymbolsSet.end())
    {
      return true;
    }
    return false;
  }

  bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);

  ASTNode NewParameterized_BooleanVar(const ASTNode& var,
                                      const ASTNode& constant);

  void TermsAlreadySeenMap_Clear(void) { TermsAlreadySeenMap.clear(); }

  // This is called before SAT solving, so only junk that isn't needed
  // after SAT solving should be cleaned out.
  void ClearAllTables(void)
  {
    NodeLetVarMap.clear();
    NodeLetVarMap1.clear();
    PLPrintNodeSet.clear();
    TermsAlreadySeenMap.clear();
    NodeLetVarVec.clear();
    ListOfDeclaredVars.clear();
  }

  DLL_PUBLIC ~STPMgr();

  // Used just via the C-Interface, to allow some nodes to be automaticaly deleted.
  vector<stp::ASTNode*> persist;

  void print_stats() const
  {

    if (_interior_unique_table.size() > 0)
    {
      std::cerr << "Interiors:" << _interior_unique_table.size() << " of ";
      std::cerr << sizeof(**_interior_unique_table.begin()) << " bytes each"
                << std::endl;
    }

    std::map<Kind, int> freq;
    for (auto it : _interior_unique_table)
    {
      freq[it->GetKind()]++;
    }

    for (auto it : freq)
      std::cerr << it.first << " " << it.second << std::endl;

    if (_symbol_unique_table.size() > 0)
    {
      std::cerr << "Symbols:" << _symbol_unique_table.size() << " of ";
      std::cerr << sizeof(**_symbol_unique_table.begin()) << " bytes each"
                << std::endl;
    }

    if (_bvconst_unique_table.size() > 0)
    {
      std::cerr << "BVConsts:" << _bvconst_unique_table.size() << " of ";
      std::cerr << sizeof(**_bvconst_unique_table.begin()) << " bytes each"
                << std::endl;
    }
  }

  ASTNodeSet getSymbols()
  {
     ASTNodeSet symbols;
     symbols.reserve(_symbol_unique_table.size());

     for (const auto& s : _symbol_unique_table)
      {
          ASTNode n(s);
          symbols.insert(n);
      }

    return symbols; //hopefully move semantics.
  }

};

} // end of namespace

#endif
