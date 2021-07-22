/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "Equalities.hpp"
#include "globals.hpp"

namespace rs {

LitID Equalities::getRepr(Lit a) {
  LitID repr = canonical[a];
  assert(repr.l != 0);
  if (a == repr.l || canonical[repr.l].l == repr.l) return repr;
  LitID reprChild = getRepr(repr.l);
  assert(toVar(reprChild.l) < toVar(repr.l));
  assert(toVar(repr.l) < toVar(a));
  if (logger) {
    assert(reprChild.id != ID_Trivial);  // as we know that canonical[repr.l]!=repr.l
    reprChild.id = logger->logResolvent(repr.id, reprChild.id);
  }
  canonical[a] = reprChild;
  return reprChild;
}

void Equalities::merge(Lit a, Lit b) {
  LitID reprA = getRepr(a);
  LitID reprB = getRepr(b);
  LitID reprAneg = getRepr(-a);
  LitID reprBneg = getRepr(-b);
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
  if (toVar(reprBl) < toVar(reprAl)) {
    canonical[reprAl] = {reprBl, reprAImpReprB};
    canonical[-reprAl] = {-reprBl, reprBImpReprA};
  } else {
    canonical[reprBl] = {reprAl, reprBImpReprA};
    canonical[-reprBl] = {-reprAl, reprAImpReprB};
  }
}

void Equalities::setNbVars(int nvars) {
  int oldNvars = canonical.reserved() / 2;
  canonical.resize(nvars, {0, ID_Trivial});
  int newNvars = canonical.reserved() / 2;
  for (Var v = oldNvars + 1; v <= newNvars; ++v) {
    canonical[v].l = v;
    canonical[-v].l = -v;
  }
}
}  // namespace rs
