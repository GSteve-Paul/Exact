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

void Equalities::merge(Lit a, Lit b, ID aImpliesB, ID bImpliesA) {
  LitID reprA = getRepr(a);
  LitID reprB = getRepr(b);
  LitID reprAneg = getRepr(-a);
  LitID reprBneg = getRepr(-b);
  if (reprA.l == reprB.l) return;  // already equal
  assert(reprA.l != -reprB.l);     // no inconsistency
  if (toVar(reprB.l) < toVar(reprA.l)) {
    canonical[reprA.l] = {
        reprB.l, logger ? logger->logResolvent(logger->logResolvent(aImpliesB, reprAneg.id), reprB.id) : ID_Trivial};
    canonical[reprAneg.l] = {
        reprBneg.l, logger ? logger->logResolvent(logger->logResolvent(bImpliesA, reprA.id), reprBneg.id) : ID_Trivial};
  } else {
    canonical[reprB.l] = {
        reprA.l, logger ? logger->logResolvent(logger->logResolvent(bImpliesA, reprBneg.id), reprA.id) : ID_Trivial};
    canonical[reprBneg.l] = {
        reprAneg.l, logger ? logger->logResolvent(logger->logResolvent(aImpliesB, reprB.id), reprAneg.id) : ID_Trivial};
  }
  assert(canonical[a].l == -canonical[-a].l);
  assert(canonical[b].l == -canonical[-b].l);
  assert(canonical[a].l == canonical[b].l);
  assert(canonical[-a].l == canonical[-b].l);
}

void Equalities::setNbVars(int nvars) {
  int oldNvars = canonical.reserved() / 2;
  canonical.resize(nvars, {0, ID_Trivial});
  for (int v = oldNvars; v <= nvars; ++v) {
    canonical[v].l = v;
    canonical[-v].l = -v;
  }
}
}  // namespace rs
