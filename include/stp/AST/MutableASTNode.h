/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb 14, 2011
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
 *  This is mutable unlike the normal ASTNode. It can be converted lazily to a
 * ASTNode.
 */

#ifndef MUTABLEASTNODE_H_
#define MUTABLEASTNODE_H_
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"

namespace stp
{
class MutableASTNode
{
  static THREAD_LOCAL vector<MutableASTNode*> all;

public:
  typedef std::unordered_set<MutableASTNode*> ParentsType;
  ParentsType parents;

  MutableASTNode(const MutableASTNode&) = delete;  
  MutableASTNode& operator=(const MutableASTNode&) = delete;

private:

  MutableASTNode(const ASTNode& n_) : n(n_) { dirty = false; }

  /* Make a mutable ASTNode graph like the ASTNode one, but with pointers back
   * up too. It's convoluted because we want a post order traversal. The root
   * node of a sub-tree will be created after its children.
   */

public:
  static MutableASTNode* build(const ASTNode& n,
                               std::unordered_map<uint64_t, MutableASTNode*>& visited)
  {
    if (visited.find(n.GetNodeNum()) != visited.end())
    {
      return visited.find(n.GetNodeNum())->second;
    }

    vector<MutableASTNode*> tempChildren;
    tempChildren.reserve(n.Degree());

    for (size_t i = 0; i < n.Degree(); i++)
    {
      tempChildren.push_back(build(n[i], visited));
    }

    MutableASTNode* mut = createNode(n);

    for (size_t i = 0; i < n.Degree(); i++)
    {
      tempChildren[i]->parents.insert(mut);
    }

    mut->children.insert(mut->children.end(), tempChildren.begin(),
                         tempChildren.end());
    visited.insert(std::make_pair(n.GetNodeNum(), mut));
    return mut;
  }

private:
  bool dirty;

public:
  bool checkInvariant()
  {
    // Symbols have no children.
    if (n.GetKind() == SYMBOL)
    {
      assert(children.size() == 0);
    }

    // all my parents have me as a child.
    for (ParentsType::iterator it = parents.begin(); it != parents.end(); it++)
    {
      vector<MutableASTNode*>::iterator it2 = (*it)->children.begin();
      bool found = false;
      for (; it2 != (*it)->children.end(); it2++)
      {
        assert(*it2 != NULL);
        if (*it2 == this)
          found = true;
      }
      assert(found);
    }

    for (size_t i = 0; i < children.size(); i++)
    {
      // call check on all the children.
      children[i]->checkInvariant();

      // all my children have me as a parent.
      assert(children[i]->parents.find(this) != children[i]->parents.end());
    }

    return true; // ignored.
  }

  MutableASTNode& getParent()
  {
    assert(parents.size() == 1);
    return **(parents.begin());
  }

  ASTNode toASTNode(stp::STPMgr* stpMgr)
  {
    if (!dirty)
      return n;

    if (children.size() == 0)
      return n;

    ASTVec newChildren;
    for (size_t i = 0; i < children.size(); i++)
      newChildren.push_back(children[i]->toASTNode(stpMgr));

    // Don't use the simplifying node factory here. Imagine CreateNode simplified
    // down,
    // from (= 1 ite( x , 1,0)) to x (say). Then this node will become a symbol,
    // but, this object will still have the equal's children. i.e. 1, and the
    // ITE.
    // So it becomes a SYMBOL with children...

    if (n.GetType() == BOOLEAN_TYPE)
    {
      n = stpMgr->hashingNodeFactory->CreateNode(n.GetKind(), newChildren);
    }
    else if (n.GetType() == BITVECTOR_TYPE)
    {
      n = stpMgr->hashingNodeFactory->CreateTerm(n.GetKind(), n.GetValueWidth(),
                                                 newChildren);
    }
    else
    {
      n = stpMgr->hashingNodeFactory->CreateArrayTerm(
          n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), newChildren);
    }

    dirty = false;
    return n;
  }

  ASTNode n;
  vector<MutableASTNode*> children;

  static MutableASTNode* createNode(ASTNode n)
  {
    MutableASTNode* result = new MutableASTNode(n);
    all.push_back(result);
    return result;
  }

  bool isSymbol() const
  {
    bool result = n.GetKind() == SYMBOL;
    if (result)
    {
      assert(children.size() == 0);
    }
    return result;
  }

  static MutableASTNode* build(ASTNode n)
  {
    std::unordered_map<uint64_t, MutableASTNode*> visited;
    return build(n, visited);
  }

  void propagateUpDirty()
  {
    if (dirty)
      return;

    dirty = true;
    for (ParentsType::iterator it = parents.begin(); it != parents.end(); it++)
      (*it)->propagateUpDirty();
  }

  void replaceWithAnotherNode(MutableASTNode* newN)
  {
    n = newN->n;
    vector<MutableASTNode*> vars;
    removeChildren(vars); // ignore the result
    children.clear();
    children.insert(children.begin(), newN->children.begin(),
                    newN->children.end());
    for (size_t i = 0; i < children.size(); i++)
      children[i]->parents.insert(this);

    propagateUpDirty();
    assert(newN->parents.size() == 0); // we don't copy 'em in you see.
    newN->removeChildren(vars);
  }

  void replaceWithVar(ASTNode newV, vector<MutableASTNode*>& variables)
  {
    assert(newV.GetKind() == SYMBOL);
    n = newV;
    removeChildren(variables);
    children.clear();
    assert(isSymbol());
    if (parents.size() == 1)
      variables.push_back(this);
    propagateUpDirty();
  }

  void removeChildren(vector<MutableASTNode*>& variables)
  {
    for (unsigned i = 0; i < children.size(); i++)
    {
      MutableASTNode* child = children[i];
      ParentsType& children_parents = child->parents;
      children_parents.erase(this);

      if (children_parents.size() == 0)
      {
        child->removeChildren(variables);
      }

      if (child->isUnconstrained())
      {
        variables.push_back(child);
      }
    }
  }

  // Variables that have >1 disjoint extract parents.
  static void getDisjointExtractVariables(vector<MutableASTNode*>& result)
  {
    const int size = all.size();
    for (int i = size - 1; i >= 0; i--)
    {
      if (!all[i]->isSymbol())
        continue;

      ParentsType* p = &(all[i]->parents);

      if (p->size() == 1)
        continue; // the regular case. Don't consider here.

      ASTNode& node = all[i]->n;
      // TODO remove alloca
      bool* found = (bool*)alloca(sizeof(bool) * node.GetValueWidth());
      for (size_t j = 0; j < node.GetValueWidth(); j++)
        found[j] = false;

      ParentsType::const_iterator it;
      for (it = p->begin(); it != p->end(); it++)
      {
        ASTNode& parent_node = (*it)->n;
        if (parent_node.GetKind() != BVEXTRACT)
          break;

        const int lb = parent_node[2].GetUnsignedConst();
        const int ub = parent_node[1].GetUnsignedConst();
        assert(lb <= ub);

        int j;
        for (j = lb; j <= ub; j++)
        {
          if (found[j])
            break;
          found[j] = true;
        }

        // if didn't make it to the finish. Then it overlaps.
        if (j <= ub)
        {
          break;
        }
      }

      if (it != p->end())
        continue;

      // All are extracts that don't overlap.
      result.push_back(all[i]);
    }
    return;
  }

  // Visit the parent before children. So that we hopefully prune parts of the
  // tree. Ie given  ( F(x_1,... x_10000) = v), where v is unconstrained,
  // we don't spend time exploring F(..), but chop it out.
  static void getAllUnconstrainedVariables(vector<MutableASTNode*>& result)
  {
    const int size = all.size();
    for (int i = size - 1; i >= 0; i--)
    {
      if (all[i]->isUnconstrained())
        result.push_back(all[i]);
    }
    return;
  }

  void getAllVariablesRecursively(vector<MutableASTNode*>& result,
                                  std::unordered_set<MutableASTNode*>& visited)
  {
    if (!visited.insert(this).second)
      return;
    if (isSymbol())
      result.push_back(this);
    const int size = children.size();
    for (int i = 0; i < size; i++)
    {
      children[i]->getAllVariablesRecursively(result, visited);
    }
  }

  bool isUnconstrained()
  {
    if (!isSymbol())
      return false;

    return parents.size() == 1;
  }

  static void cleanup()
  {
    for (size_t i = 0; i < all.size(); i++)
      delete all[i];
    all.clear();
  }
};
}

#endif /* MUTABLEASTNODE_H_ */
