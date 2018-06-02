/*********************                                                        */
/*! \file sygus_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif
 **/

#include "theory/quantifiers/sygus/sygus_unif.h"

#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusUnif::SygusUnif() : d_qe(nullptr), d_tds(nullptr) {}
SygusUnif::~SygusUnif() {}

void SygusUnif::initializeCandidate(
    QuantifiersEngine* qe,
    Node f,
    std::vector<Node>& enums,
    std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  d_qe = qe;
  d_tds = qe->getTermDatabaseSygus();
  d_candidates.push_back(f);
  // initialize the strategy
  d_strategy[f].initialize(qe, f, enums);
}

bool SygusUnif::constructSolution(std::vector<Node>& sols,
                                  std::vector<Node>& lemmas)
{
  // initialize a call to construct solution
  initializeConstructSol();
  for (const Node& f : d_candidates)
  {
    // initialize a call to construct solution for function f
    initializeConstructSolFor(f);
    // call the virtual construct solution method
    Node e = d_strategy[f].getRootEnumerator();
    Node sol = constructSol(f, e, role_equal, 1, lemmas);
    if (sol.isNull())
    {
      return false;
    }
    sols.push_back(sol);
  }
  return true;
}

Node SygusUnif::constructBestSolvedTerm(const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestStringSolvedTerm(const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestSolvedConditional(const std::vector<Node>& solved)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestConditional(const std::vector<Node>& conds)
{
  Assert(!conds.empty());
  double r = Random::getRandom().pickDouble(0.0, 1.0);
  unsigned cindex = r * conds.size();
  if (cindex > conds.size())
  {
    cindex = conds.size() - 1;
  }
  return conds[cindex];
}

Node SygusUnif::constructBestStringToConcat(
    const std::vector<Node>& strs,
    const std::map<Node, unsigned>& total_inc,
    const std::map<Node, std::vector<unsigned>>& incr)
{
  Assert(!strs.empty());
  std::vector<Node> strs_tmp = strs;
  std::random_shuffle(strs_tmp.begin(), strs_tmp.end());
  // prefer one that has incremented by more than 0
  for (const Node& ns : strs_tmp)
  {
    const std::map<Node, unsigned>::const_iterator iti = total_inc.find(ns);
    if (iti != total_inc.end() && iti->second > 0)
    {
      return ns;
    }
  }
  return strs_tmp[0];
}

void SygusUnif::indent(const char* c, int ind)
{
  if (Trace.isOn(c))
  {
    for (int i = 0; i < ind; i++)
    {
      Trace(c) << "  ";
    }
  }
}

void SygusUnif::print_val(const char* c, std::vector<Node>& vals, bool pol)
{
  if (Trace.isOn(c))
  {
    for (unsigned i = 0; i < vals.size(); i++)
    {
      Trace(c) << ((pol ? vals[i].getConst<bool>() : !vals[i].getConst<bool>())
                       ? "1"
                       : "0");
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
