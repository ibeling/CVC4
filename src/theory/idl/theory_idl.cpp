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
	  d_varList(c),
	  d_allNodes(c),
	  d_atomList(c),
	  d_firstAtom(c)
      {
	 	cout << "theory IDL constructed" << endl;
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
	    	Assert(node.getKind() != kind::NOT);
		AtomListEntry atomentry;
		if (d_atomList.size() == 0)
		  {
		    d_firstAtom.set(0);
		    atomentry.prevSteps = 0;
		  }
		else {
		  atomentry.prevSteps = 1;
		  		AtomListEntry lastEntry = d_atomList[d_atomList.size() - 1];
		lastEntry.nextSteps = 1;
		d_atomList.set(lastEntry.pos, lastEntry);
		}
		atomentry.nextSteps = 0;
		atomentry.atom = node;
		atomentry.pos = d_atomList.size();
		d_atomList.push_back(atomentry);
		d_atomToIndexMap[node] = d_atomList.size() - 1;
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
	//	  cout << "Printing assertion list " << endl;
	//cout << "The first index is  " << d_firstAtom.get() << endl;

	bool value;
	AtomListEntry entry = d_atomList.get(d_firstAtom.get());
	while (entry.nextSteps != 0) {
	  TNode node = entry.atom;
	  //	  cout << "considering " << node << endl;
	  // 	  cout << "next " << entry.nextSteps << " prev " << entry.prevSteps << " pos " << entry.pos << endl; 

	    bool alreadyAssigned = d_valuation.hasSatValue(node, value);
	    Assert(!alreadyAssigned);
	    IDLAssertion idl_assertion(node);
	    TNode x = idl_assertion.getX();
	    TNode y = idl_assertion.getY();
	    Integer c = idl_assertion.getC();
	    TNodePair xy = std::make_pair(x, y);
	    if (d_valid.contains(xy) && (d_distances[xy].get() <= c)) {
	      d_indices1[node] = d_indices[xy];
	      // 	      cout << "propagating " << node << endl;
	      d_out->propagate( node );
	    }

	    TNodePair yx = std::make_pair(y, x);
	    if (d_valid.contains(yx) && (d_distances[yx].get() < -c)) {
				TNode nn;
				if ( d_atomToNegAtomMap.find(node) == d_atomToNegAtomMap.end() )
				{
					Node notNode = NodeManager::currentNM()->mkNode(kind::NOT, node);
					d_atomToNegAtomMap[node] = notNode;
					nn = notNode;
				} else {
					nn = d_atomToNegAtomMap[node];
				}
	      d_indices1[nn] = d_indices[yx];
	      // 	      	      cout << "propagating " << notNode << endl;
	      d_out->propagate(nn);
	    }

	    unsigned nextIndex = entry.pos + entry.nextSteps;
	    // 	    cout << "next Index  " << nextIndex << endl;
	    
	    entry = d_atomList.get(nextIndex);
	}
      }

      void TheoryIdl::getPath(unsigned idx, std::vector<TNode>& reasonslist) {
	const TrailEntry& entry = d_trail[idx];

	if (entry.reasons.size() == 0) {
	  reasonslist.push_back(entry.original);
	} else {
	  for (unsigned i = 0; i < entry.reasons.size(); ++i)
	    {
	      getPath(entry.reasons[i], reasonslist);
	    }
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
	  TNode assertiontnode = assertion.assertion;
	  //	  cout << "Asserted " << assertiontnode << endl;
	  if (assertiontnode.getKind() == kind::NOT)
	    {
	      //	      cout << "assert " << assertiontnode << endl;

				assertiontnode = assertion.assertion[0];
				d_atomToNegAtomMap[assertiontnode] = assertion.assertion;
	    }

	  //assertiontnode is now an atom

	  //	  cout << "asserting atom " << assertiontnode << endl;
	  unsigned index = d_atomToIndexMap[assertiontnode];
	  //	  cout << "deleting entry at index " << index << endl;
	  AtomListEntry entry = d_atomList.get(index);

	  //	  cout << entry.nextSteps << " " << entry.prevSteps << " " << entry.pos << " " << entry.atom << endl;
	  

      
	  // delete from list
	 
	  if (entry.prevSteps != 0)
	    {
	      AtomListEntry prevEntry = d_atomList.get(entry.pos - entry.prevSteps);
	      prevEntry.nextSteps = prevEntry.nextSteps + entry.nextSteps;
	      d_atomList.set(prevEntry.pos, prevEntry);
	    }
	  if (entry.nextSteps != 0)
	    {
	      AtomListEntry nextEntry = d_atomList.get(entry.pos + entry.nextSteps);
	      nextEntry.prevSteps = nextEntry.prevSteps + entry.prevSteps;
	      d_atomList.set(nextEntry.pos, nextEntry);
	    }

	  // delete first atom:
	  // firstIndex has to be updated. (if also last atom, set to end)
	  // besides this, next entry has to have prev set to zero.
	  unsigned firstIndex = d_firstAtom.get();
	  if (index == firstIndex)
	    {
	      if (entry.nextSteps != 0) {
		AtomListEntry afterFirst = d_atomList.get(entry.nextSteps + index);
		afterFirst.prevSteps = 0;
		d_atomList.set(entry.nextSteps + index, afterFirst);
	      }
	      d_firstAtom.set(entry.nextSteps + index);
	    }


	  //	  cout << "Asserting! " << endl;
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
	  //	  cout << "redundant!" << endl;
	  return true;
	}

	// Put assertion on  the trail.
	TrailEntry assertionEntry;
	assertionEntry.x = x;
	assertionEntry.y = y;
	assertionEntry.c = c;
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
		if ( z != x ) {
		  Assert(d_indices.contains(zx));
		  zvEntry.reasons.push_back(d_indices[zx]);
		}
		zvEntry.reasons.push_back(xyIndex);
		if ( y != v ) {
		  Assert(d_indices.contains(yv));
		  zvEntry.reasons.push_back(d_indices[yv]);
		}
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


	      }
	    }
	  }
	}

	return true;
      }

    } /* namepsace CVC4::theory::idl */
  } /* namepsace CVC4::theory */
} /* namepsace CVC4 */
