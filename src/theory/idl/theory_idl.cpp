/*********************                                                        */
/*! \file theory_idl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
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

#include "theory/idl/theory_idl.h"

#include <queue>
#include <set>

#include "options/idl_options.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace idl {

TheoryIdl::TheoryIdl(context::Context* c, context::UserContext* u,
                     OutputChannel& out, Valuation valuation,
                     const LogicInfo& logicInfo)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo),
      d_trail(c),
      d_distances(c),
      d_valid(c),
      d_propagationEdges(c),
      d_indices(c),
      d_indices1(c),
      d_varList(c) {
  // cout << "theory IDL constructed" << endl;
}

void TheoryIdl::preRegisterTerm(TNode node) {
  Assert(node.getKind() != kind::NOT);
  if (node.isVar()) {
    d_varList.push_back(node);
    d_distances.insertAtContextLevelZero(std::make_pair(node, node), 0);
    d_valid.insertAtContextLevelZero(std::make_pair(node, node));
    return;
  } else {
    IDLAssertion idl_assertion(node);
    if (idl_assertion.ok()) {
      TNodePair xy = std::make_pair(idl_assertion.getX(), idl_assertion.getY());
      std::vector<TNode> prop_edge;
      if (d_propagationEdges.contains(xy)) {
        prop_edge = d_propagationEdges[xy].get();
      }
      prop_edge.push_back(node);
      d_propagationEdges[xy] = prop_edge;

      Node neg = NodeManager::currentNM()->mkNode(kind::NOT, node);
      IDLAssertion neg_idl_assertion(neg);
      TNodePair xyneg =
          std::make_pair(neg_idl_assertion.getX(), neg_idl_assertion.getY());
      std::vector<TNode> neg_prop_edge;
      if (d_propagationEdges.contains(xyneg)) {
        neg_prop_edge = d_propagationEdges[xyneg].get();
      }
      neg_prop_edge.push_back(neg);
      d_propagationEdges[xyneg] = neg_prop_edge;

      // cout << "registered " << node << " with corresponding neg " << neg <<
      // endl;
    }
  }
}

void TheoryIdl::presolve() {
  // Debug("theory::idl") << "TheoryIdl::preSolve(): d_numVars = " << d_numVars
  // << std::endl;
}

void TheoryIdl::postsolve() {
  // Debug("theory::idl") << "TheoryIdl::postSolve()" << std::endl;
}

Node TheoryIdl::ppRewrite(TNode atom) {
  Assert(atom.getKind() != kind::NOT);
  if (atom.getKind() == kind::EQUAL) {
    Node leq = NodeBuilder<2>(kind::LEQ) << atom[0] << atom[1];
    Node geq = NodeBuilder<2>(kind::GEQ) << atom[0] << atom[1];
    Node rewritten = Rewriter::rewrite(leq.andNode(geq));
    return rewritten;
  }
  return atom;
}

void TheoryIdl::propagate(Effort level) {
  // Propagation is done when new shortest paths are discovered.
}

void TheoryIdl::getPath(unsigned idx, std::vector<TNode>& reasonslist) {
  const TrailEntry& entry = d_trail[idx];
  if (entry.numReasons == 0) {
    reasonslist.push_back(entry.original);
  } else if (entry.numReasons == 2) {
    getPath(entry.reason1, reasonslist);
    getPath(entry.reason2, reasonslist);
  } else if (entry.numReasons == 3) {
    getPath(entry.reason1, reasonslist);
    getPath(entry.reason2, reasonslist);
    getPath(entry.reason3, reasonslist);
  }
}

Node TheoryIdl::explain(TNode n) {
  Assert(d_indices1.contains(n));
  unsigned idx = d_indices1[n];

  std::vector<TNode> reasonslist;
  getPath(idx, reasonslist);

  Node explanation;
  if (reasonslist.size() > 1) {
    explanation = NodeManager::currentNM()->mkNode(kind::AND, reasonslist);
  } else {
    explanation = reasonslist[0];
  }

  return explanation;
}

void TheoryIdl::check(Effort level) {
  if (done() && !fullEffort(level)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  while (!done()) {
    // Get the next assertion
    Assertion assertion = get();
    Debug("theory::idl") << "TheoryIdl::check(): processing "
                         << assertion.assertion << std::endl;
    IDLAssertion idl_assertion(assertion);
    // cout << "doing assertion " << assertion << endl;
    bool ok = processAssertion(idl_assertion, assertion);
    Debug("theory::idl") << "assertion " << assertion << endl;
    if (!ok) {
      // cout << "conflict! " << assertion << endl;
      // d_propagationQueue.clear();
      std::vector<TNode> reasonslist;
      TNodePair yx = std::make_pair(idl_assertion.getY(), idl_assertion.getX());      
      getPath(d_indices[yx], reasonslist);
      // cout << "CONFLICT was " << valgp << " and size = " <<
      // reasonslist.size() << endl;
      reasonslist.push_back(idl_assertion.getTNode());
      Node conflict = NodeManager::currentNM()->mkNode(kind::AND, reasonslist);
      // cout << "CONFLICT " << conflict << endl;
      d_out->conflict(conflict);
      return;
    }
  }
}

bool TheoryIdl::processAssertion(const IDLAssertion& assertion, const TNode& original) {
  Assert(assertion.ok());

  TNode x = assertion.getX();
  TNode y = assertion.getY();
  Integer c = assertion.getC();
  TNodePair xy = std::make_pair(x, y);
  TNodePair yx = std::make_pair(y, x);

  // Check whether we introduce a negative cycle.
  if (d_valid.contains(yx) && ((d_distances[yx].get() + c) < 0)) {
    return false;
  }

  // Check whether assertion is redundant
  if (d_valid.contains(xy) && (d_distances[xy].get() <= c)) {
    return true;
  }

  // Put assertion on  the trail.
  TrailEntry assertionEntry;
  assertionEntry.x = x;
  assertionEntry.y = y;
  assertionEntry.c = c;
  assertionEntry.numReasons = 0;
  assertionEntry.original = original;
  d_trail.push_back(assertionEntry);
  unsigned xyIndex = d_trail.size() - 1;

  // Find shortest paths incrementally
  std::vector<TNode> valid_vars;
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair yz = std::make_pair(y, z);
    TNodePair xz = std::make_pair(x, z);  // TODO: eliminate double lookups
    if (d_valid.contains(yz) &&
        ((!d_valid.contains(xz)) ||
         ((c + d_distances[yz].get()) < d_distances[xz].get()))) {
      valid_vars.push_back(z);
    }
  }
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair zx = std::make_pair(z, x);
    TNodePair zy = std::make_pair(z, y);
    if (d_valid.contains(zx) &&
        ((!d_valid.contains(zy)) ||
         ((c + d_distances[zx].get()) < d_distances[zy].get()))) {
      for (unsigned j = 0; j < valid_vars.size(); ++j) {
        TNode v = valid_vars[j];
        if (v == z) {
          continue;
        }
        TNodePair yv = std::make_pair(y, v);
        TNodePair zv = std::make_pair(z, v);
        // Path z ~ x -> y ~ v
        // Three reasons: this assertion, the reason for z ~ x, and the reason
        // for y ~ v.
        Integer dist = c + d_distances[zx].get() + d_distances[yv].get();
        if ((!d_valid.contains(zv)) || (dist < d_distances[zv].get())) {
          if (!d_valid.contains(zv)) {
            d_distances[zv] = dist;
            d_valid.insert(zv);
          } else {
            d_distances[zv] = dist;
          }

          TrailEntry zvEntry;
          zvEntry.x = z;
          zvEntry.y = v;
          zvEntry.c = c;
          unsigned numReasons = 1;
          unsigned reason1, reason2, reason3;
          reason1 = xyIndex;
          if ( z != x ) {
            numReasons++;
            reason2 = d_indices[zx];
          }
          if ( y != v ) {
            numReasons++;
            reason3 = d_indices[yv];
          }
          zvEntry.numReasons = numReasons;
          zvEntry.reason1 = reason1;
          zvEntry.reason2 = reason2;
          zvEntry.reason3 = reason3;
          if ( z != x || y != v )
          {
            d_trail.push_back(zvEntry);
            d_indices[zv] = d_trail.size() - 1;  
          }
          else
          {
            d_indices[zv] = xyIndex;
          }

          // assert, assert, infer, prop, prop
          // the infer trail entry is not needed.
          // to trace back:
          // prop(i1, i2, i3)
          // i2 will be an assert (x -> y)
          // need to set i1 ~> i2 or i2 ~> i3 to an inferred, non propagated trail entry.

          // 0 assert: x - y <= 3
          // infer: shortest path from x-> y new length 3, x - y <= 3 <-- redundant
          // 1 assert: y - z <= 5
          // infer: shortest path y -> z new length 5, y - z <= 5 <-- redundant
          // 2 infer: shortest path x -> z new length 8, x - z <= 8.
          // the reason: x ~> y -> z
          // reason indices 0 (current shortest paths matrix), 1 (the asserted edge)
          // 3 infer: propagate path, x - z <= 10
          // reason indices the same.

          // Propagate anything implied by the new shortest path
          if (d_propagationEdges.contains(zv)) {
            const std::vector<TNode>& prop_assertions =
                d_propagationEdges[zv].get();
            for (unsigned k = 0; k < prop_assertions.size(); ++k) {
              IDLAssertion propagation_assertion =
                  IDLAssertion(prop_assertions[k]);
              bool value;
              if ((dist <= propagation_assertion.getC()) &&
                  !d_valuation.hasSatValue(propagation_assertion.getTNode(),
                                           value)) {
                d_out->propagate(propagation_assertion.getTNode());
                d_indices1[prop_assertions[k]] = d_indices[zv];
              }
            }
          }
        }
      }
    }
  }

  return true;
}

} /* namepsace CVC4::theory::idl */
} /* namepsace CVC4::theory */
} /* namepsace CVC4 */
