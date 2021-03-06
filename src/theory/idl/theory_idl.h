/*********************                                                        */
/*! \file theory_idl.h
** \verbatim
** Top contributors (to current version):
**   Dejan Jovanovic, Morgan Deters, Paul Meng
** This file is part of the CVC4 project.
** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file COPYING in the top-level source
** directory for licensing information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#pragma once

#include "cvc4_private.h"

#include "theory/theory.h"

#include "idl_assertion.h"

#include "context/cdvector.h"

namespace CVC4 {
namespace theory {
namespace idl {

class AtomListEntry {
 public:
  unsigned nextSteps;
  unsigned prevSteps;
  unsigned pos;
  IDLAssertion idl_assertion;
  /* TNode atom; */
  /* unsigned x; */
  /* unsigned y; */
  /* Integer c; */
};

class TrailEntry {
public:
  TrailEntry() {
    reasons.reserve(3);
  }
  
  TNode original;
  std::vector<unsigned> reasons;
};

/**
 * Handles integer difference logic (IDL) constraints.
 */
class TheoryIdl : public Theory {


  /** Process a new assertion */
  bool processAssertion(const IDLAssertion& assertion, const TNode& original);

  typedef std::pair<TNode, TNode> TNodePair;

  typedef context::CDHashMap<TNodePair, Integer, TNodePairHashFunction>
      TNodePairToIntegerCDMap;
  typedef context::CDHashMap<TNodePair, std::vector<TNode>,
                             TNodePairHashFunction>
      TNodePairToTNodeVectorCDMap;
  typedef context::CDHashMap<TNode, unsigned, TNodeHashFunction>
      TNodeToUnsignedCDMap;
  typedef context::CDHashMap<TNodePair, unsigned, TNodePairHashFunction>
      TNodePairToUnsignedCDMap;
  typedef context::CDHashSet<TNodePair, TNodePairHashFunction> TNodePairCDSet;
  typedef context::CDList<TrailEntry> TrailType;
  typedef context::CDList<TNode> TNodeCDList;

  bool donePreprocess = false;

  /** Trail of literals, either asserted or inferred **/
  TrailType d_trail;

  /** Shortest path matrix **/
  // context::CDVector<int> d_distances;
  context::CDHashMap<unsigned, Integer> d_distances;
  
  // context::CDVector<bool> d_valid;
  // context::CDO<bool>** d_valid;
  context::CDHashMap<TNode, unsigned, TNodeHashFunction> d_varMap;

  /** Edges associated to a given pair for propagation **/
  TNodePairToTNodeVectorCDMap d_propagationEdges;

  /** The index in the trail at which a distance was obtained **/
  // context::CDVector<unsigned> d_indices;
  context::CDHashMap<unsigned, unsigned> d_indices;

  /** The index in the trail at which a literal was asserted or propagated **/
  TNodeToUnsignedCDMap d_indices1;

  TNodeCDList d_varList;

  context::CDList<std::set<TNode> > d_allNodes;
  std::set<TNode> d_allNodesSet;

  context::CDVector<AtomListEntry> d_atomList;
  context::CDO<unsigned> d_firstAtom;
  std::unordered_map<TNode, unsigned, TNodeHashFunction> d_atomToIndexMap;

  unsigned d_numVars;
  bool d_needFakeVariable;

  context::Context* d_context;

inline unsigned pairToIndex(unsigned i, unsigned j)
{
  return i * d_numVars + j;
}

inline unsigned getIndexFromVarTNode(const TNode &idl_assertion_x)
{
  return idl_assertion_x.isNull() ? (d_numVars - 1) : d_varMap[idl_assertion_x];
}

public:
  /** Theory constructor. */
  TheoryIdl(context::Context* c, context::UserContext* u, OutputChannel& out,
            Valuation valuation, const LogicInfo& logicInfo);

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  /** Clean up the solving data structures */
  void postsolve();

  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom) override;

  /** Check the assertions for satisfiability */
  void check(Effort effort) override;

  void propagate(Effort level);

  void getPath(unsigned idx, std::vector<TNode>& reasonslist);

  Node explain(TNode n);

  /** Identity string */
  std::string identify() const override { return "THEORY_IDL"; }

}; /* class TheoryIdl */
} /* CVC4::theory::idl namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
