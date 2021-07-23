/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "Equalities.hpp"
#include "Solver.hpp"
#include "globals.hpp"

namespace rs {

const Repr& Equalities::getRepr(Lit a) {
  Repr& repr = canonical[a];
  assert(repr.l != 0);
  if (a == repr.l || canonical[repr.l].l == repr.l) return repr;
  assert(toVar(repr.l) < toVar(a));
  const Repr& reprChild = getRepr(repr.l);
  assert(toVar(reprChild.l) < toVar(repr.l));
  repr.l = reprChild.l;
  if (logger) {
    assert(reprChild.id != ID_Trivial);  // as we know that canonical[repr.l]!=repr.l
    repr.id = logger->logResolvent(repr.id, reprChild.id);
  }
  return repr;
}

void Equalities::merge(Lit a, Lit b) {
  const Repr& reprA = getRepr(a);
  const Repr& reprB = getRepr(b);
  const Repr& reprAneg = getRepr(-a);
  const Repr& reprBneg = getRepr(-b);
  assert(reprA.l == -reprAneg.l);
  assert(reprB.l == -reprBneg.l);
  Lit reprAl = reprA.l;
  Lit reprBl = reprB.l;
  if (reprAl == reprBl) return;  // already equal
  assert(reprAl != -reprBl);     // no inconsistency
  ++stats.NPROBINGEQS;
  auto [reprAImpReprB, reprBImpReprA] =
      logger ? logger->logEquality(a, b, reprA.id, reprAneg.id, reprB.id, reprBneg.id, reprAl, reprBl)
             : std::pair<ID, ID>{ID_Trivial, ID_Trivial};
  Repr& reprAlRepr = canonical[reprAl];
  Repr& reprAlNegRepr = canonical[-reprAl];
  Repr& reprBlRepr = canonical[reprBl];
  Repr& reprBlNegRepr = canonical[-reprBl];
  if (toVar(reprBl) < toVar(reprAl)) {
    reprBlRepr.equals.push_back(reprAl);
    reprBlNegRepr.equals.push_back(-reprAl);
    aux::appendTo(reprBlRepr.equals, reprAlRepr.equals);
    aux::appendTo(reprBlNegRepr.equals, reprAlNegRepr.equals);
    reprAlRepr = {reprBl, reprAImpReprB, {}};
    reprAlNegRepr = {-reprBl, reprBImpReprA, {}};
  } else {
    reprAlRepr.equals.push_back(reprBl);
    reprAlNegRepr.equals.push_back(-reprBl);
    aux::appendTo(reprAlRepr.equals, reprBlRepr.equals);
    aux::appendTo(reprAlNegRepr.equals, reprBlNegRepr.equals);
    reprBlRepr = {reprAl, reprBImpReprA, {}};
    reprBlNegRepr = {-reprAl, reprAImpReprB, {}};
  }
}

bool Equalities::isCanonical(Lit l) { return getRepr(l).l == l; }

void Equalities::setNbVars(int nvars) {
  int oldNvars = canonical.reserved() / 2;
  canonical.resize(nvars, {0, ID_Trivial, {}});
  int newNvars = canonical.reserved() / 2;
  for (Var v = oldNvars + 1; v <= newNvars; ++v) {
    canonical[v].l = v;
    canonical[-v].l = -v;
  }
}

State Equalities::propagate() {
  for (; nextTrailPos < (int)solver.trail.size(); ++nextTrailPos) {
    Lit l = solver.trail[nextTrailPos];
    assert(isTrue(solver.getLevel(), l));
    const Repr& repr = getRepr(l);
    if (!isTrue(solver.getLevel(), repr.l)) {
      if (solver.learnClause({-l, repr.l}, Origin::EQUALITY, repr.id) == ID_Unsat) return State::UNSAT;
      return State::FAIL;
    }
    assert(solver.getLevel()[l] == solver.getLevel()[repr.l]);
    for (Lit ll : repr.equals) {
      if (!isTrue(solver.getLevel(), ll)) {
        assert(getRepr(ll).l == l);
        if (solver.learnClause({-l, ll}, Origin::EQUALITY, getRepr(-ll).id) == ID_Unsat) return State::UNSAT;
      }
      assert(solver.getLevel()[l] == solver.getLevel()[ll]);
      return State::FAIL;
    }
  }
  return State::SUCCESS;
}

void Equalities::notifyBackjump(int newTrailSize) { nextTrailPos = std::min(nextTrailPos, newTrailSize); }

}  // namespace rs
