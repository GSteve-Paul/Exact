/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2024 Jo Devriendt, Nonfiction Software

Exact is free software: you can redistribute it and/or modify it under
the terms of the GNU Affero General Public License version 3 as
published by the Free Software Foundation.

Exact is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public
License version 3 for more details.

You should have received a copy of the GNU Affero General Public
License version 3 along with Exact. See the file used_licenses/COPYING
or run with the flag --license=AGPLv3. If not, see
<https://www.gnu.org/licenses/>.
**********************************************************************/

/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

/**********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**********************************************************************/

#include "Optimization.hpp"
#include "Global.hpp"
#include "IntProg.hpp"
#include "Solver.hpp"
#include "constraints/ConstrExp.hpp"
#include <sys/resource.h>

namespace xct {

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::LazyVar(Solver& slvr, const Ce32& cardCore, Var startVar, const SMALL& m, const LARGE& upperBnd)
    : solver(slvr), coveredVars(cardCore->getDegree()), upperBound(cardCore->nVars()), mult(m) {
  setUpperBound(upperBnd);
  assert(remainingVars() > 0);
  cardCore->copyTo(atLeast);
  atLeast.orig = Origin::COREGUIDED;
  atLeast.toNormalFormLit();
  assert(atLeast.rhs == cardCore->getDegree());
  atMost.orig = Origin::COREGUIDED;
  atMost.rhs = -atLeast.rhs;
  atMost.terms.reserve(atLeast.size() + 1);
  for (auto& t : atLeast.terms) {
    atMost.terms.emplace_back(-t.c, t.l);
  }
  currentVar = startVar;
  atLeast.terms.emplace_back(-1, startVar);
  atMost.terms.emplace_back(remainingVars(), startVar);
  ++coveredVars;
}

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::~LazyVar() {
  solver.dropExternal(atLeastID, false, false);
  solver.dropExternal(atMostID, false, false);
}

template <typename SMALL, typename LARGE>
int LazyVar<SMALL, LARGE>::remainingVars() const {
  return upperBound - coveredVars;
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::setUpperBound(const LARGE& normalizedUpperBound) {
  assert(normalizedUpperBound >= 0);
  assert(mult > 0);
  const LARGE tmp = normalizedUpperBound / mult;
  if (tmp < upperBound) upperBound = static_cast<int>(tmp);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addVar(Var v) {
  currentVar = v;
  atLeast.terms.emplace_back(-1, v);
  Term32& last = atMost.terms.back();
  last = {1, last.l};
  atMost.terms.emplace_back(remainingVars(), v);
  ++coveredVars;
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addAtLeastConstraint() {
  assert(atLeast.terms.back().l == currentVar);
  solver.dropExternal(atLeastID, true, false);  // TODO: should old constraints be force deleted?
  solver.addConstraint(atLeast);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addAtMostConstraint() {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, true, false);
  solver.addConstraint(atMost);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addSymBreakingConstraint(Var prevvar) const {
  assert(prevvar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  solver.addBinaryConstraint(prevvar, -currentVar, Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addFinalAtMost() {
  solver.dropExternal(atMostID, true, false);
  Term32& last = atMost.terms.back();
  last = {1, last.l};
  solver.addConstraint(atMost);
}

OptimizationSuper::OptimizationSuper(Solver& s, const bigint& os, const IntSet& assumps)
    : solver(s), global(s.global), offset(os), assumptions(assumps) {}

Optim OptimizationSuper::make(const IntConstraint& ico, Solver& solver, const IntSet& assumps) {
  CeArb obj = solver.global.cePools.takeArb();
  ico.toConstrExp(obj, true);
  obj->removeEqualities(solver.getEqualities());
  obj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  bigint offs = -obj->getDegree();
  obj->addRhs(offs);
  assert(obj->getDegree() == 0);
  solver.setObjective(obj);

  bigint maxVal = obj->absCoeffSum();
  // The argument that maxVal is a safe upper bound is that we may *increase* the coefficient of assumption literals
  // during core-based reformulation, but never higher than the original coefficient sum.
  // E.g., ax+by+cz
  // assuming q to false may yield the sequence of cores q+x>=1, q+y>=1, q+z>=1.
  // these will lead to the following reformulation equalities: x=u+~q, y=v+~q, z=w+~q.
  // with final reformulation (a+b+c)~q + au + bv + cz.
  // Sum of coefficients is a sensible upper bound, since the assumption of the corresponding literal to true would
  // mean that the objective is at its maximal value.
  //
  // Since q is assumed to false (user assumption) and auxiliaries u, v, w are assumed to false (reformulated objective
  // literals), the only cores that will increase q at the expense of u, v, w are those where both q and u, v, w are
  // positive. However, since q and u, v, w have opposed polarity in the reformulation equalities, no such cores exist.
  // Hence, q's coefficient will not be reformulated beyond the sum of coefficients.
  // TODO: get a more rigorous proof from this argument?

  if (maxVal <= static_cast<bigint>(limitAbs<int, long long>())) {  // TODO: try to internalize this check in ConstrExp
    Ce32 o = solver.global.cePools.take32();
    obj->copyTo(o);
    return std::make_shared<Optimization<int, long long>>(o, solver, offs, assumps);
  }
  if (maxVal <= static_cast<bigint>(limitAbs<long long, int128>())) {
    Ce64 o = solver.global.cePools.take64();
    obj->copyTo(o);
    return std::make_shared<Optimization<long long, int128>>(o, solver, offs, assumps);
  }
  // TODO: below yielded a bug during coreguided search - not sure where. Multiplying two coefficients?
  //  if (maxVal <= static_cast<bigint>(limitAbs<int128, int128>())) {
  //    Ce96 o = solver.global.cePools.take96();
  //    obj->copyTo(o);
  //    return std::make_shared<Optimization<int128, int128>>(o, solver, offs, assumps);
  //  }
  if (maxVal <= static_cast<bigint>(limitAbs<int128, int256>())) {
    Ce128 o = solver.global.cePools.take128();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int256>>(o, solver, offs, assumps);
  }
  CeArb o = solver.global.cePools.takeArb();
  obj->copyTo(o);
  return std::make_shared<Optimization<bigint, bigint>>(o, solver, offs, assumps);
}

template <typename SMALL, typename LARGE>
void simplifyAssumps(CePtr<SMALL, LARGE>& c, const IntSet& assumps) {
  for (const Lit l : assumps.getKeys()) {  // remove assumptions from objective
    const Var v = toVar(l);
    if (c->hasVar(v)) {
      if (c->hasLit(l)) c->addRhs(aux::abs(c->coefs[v]));
      c->coefs[v] = 0;
    }
  }
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(const CePtr<SMALL, LARGE>& obj, Solver& s, const bigint& os,
                                         const IntSet& assumps)
    : OptimizationSuper(s, os, assumps),
      origObj(obj),
      lower_bound(0),
      upper_bound(obj->absCoeffSum() + 1),
      lastUpperBound(ID_Undef),
      lastLowerBound(ID_Undef),
      lastReformUpperBound(ID_Undef),
      boundingVal(0),
      boundingVar(0) {
  assert(origObj->getDegree() == 0);
  global.logger.logObjective(origObj);
  if (global.options.optCoreguided) {
    reformObj = global.cePools.take<SMALL, LARGE>();
    origObj->copyTo(reformObj);
    reformObj->removeEqualities(solver.getEqualities());
    simplifyAssumps(reformObj, assumptions);
    reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());

    lower_bound = -reformObj->getDegree();
  }
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::~Optimization() {
  // NOTE: do not make the upper bound erasable, otherwise the solver is not guaranteed to remain optimal
  solver.dropExternal(lastUpperBound, false, false);
  solver.dropExternal(lastLowerBound, true, false);
  solver.dropExternal(lastReformUpperBound, true, false);
}

template <typename SMALL, typename LARGE>
bigint Optimization<SMALL, LARGE>::getUpperBound() const {
  return offset + upper_bound;
}
template <typename SMALL, typename LARGE>
bigint Optimization<SMALL, LARGE>::getLowerBound() const {
  return offset + lower_bound;
}
template <typename SMALL, typename LARGE>
CeSuper Optimization<SMALL, LARGE>::getOrigObj() const {
  return origObj;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::printObjBounds(bool upperImproved) {
  if (!solver.objectiveIsSet()) return;
  if (!global.options.uniformOut && (global.options.fileFormat.is("opb") || global.options.fileFormat.is("wbo") ||
                                     global.options.fileFormat.is("wcnf"))) {
    if (upperImproved) std::cout << "o " << getUpperBound() << std::endl;
    return;
  }
  if (global.options.verbosity.get() == 0) return;
  std::cout << "c     bounds ";
  if (solver.foundSolution()) {
    std::cout << getUpperBound();
  } else {
    std::cout << "-";
  }
  std::cout << " >= " << getLowerBound() << " @ " << global.stats.getTime() << ", " << global.stats.NCONFL.z << "\n";
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::checkLazyVariables() {
  // TODO: take *upper* bound on reformed objective into account.
  // E.g.: objective x+y+z+w =< 3 for core x+y+z+w >= 1 means we can rewrite to x+y+z+w = 1+a+b instead of = 1+a+b+c
  for (int i = 0; i < (int)lazyVars.size(); ++i) {
    LazyVar<SMALL, LARGE>& lv = *lazyVars[i];
    if (reformObj->getLit(lv.currentVar) == 0) {
      lv.setUpperBound(upper_bound);
      if (lv.remainingVars() == 0 ||
          isUnit(solver.getLevel(), -lv.currentVar)) {  // binary constraints make all new auxiliary variables unit
        lv.addFinalAtMost();
        plf::single_reorderase(lazyVars, lazyVars.begin() + i);  // fully expanded, no need to keep in memory
        --i;
      } else {  // add auxiliary variable
        int newN = solver.addVar(false);
        Var oldvar = lv.currentVar;
        lv.addVar(newN);
        // reformulate the objective
        reformObj->addLhs(lv.mult, newN);
        // add necessary lazy constraints
        lv.addAtLeastConstraint();
        lv.addAtMostConstraint();
        lv.addSymBreakingConstraint(oldvar);
        if (lv.remainingVars() == 0) {
          plf::single_reorderase(lazyVars, lazyVars.begin() + i);  // fully expanded, no need to keep in memory
          --i;
        }
      }
    }
  }
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::addLowerBound() {
  CePtr<SMALL, LARGE> aux = global.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->orig = Origin::LOWERBOUND;
  aux->addRhs(lower_bound);
  assert(static_cast<bigint>(limitAbs<SMALL, LARGE>()) == 0 ||
         aux->getDegree() < static_cast<bigint>(limitAbs<SMALL, LARGE>()));
  for (Lit l : assumptions.getKeys()) {
    aux->addLhs(static_cast<SMALL>(aux->getDegree()), -l);  // bound only holds under assumptions
  }
  solver.dropExternal(lastLowerBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux);
  lastLowerBound = res.second;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::addReformUpperBound(bool deletePrevious) {
  if (!reformObj || reformObj->vars.empty()) return;
  CePtr<SMALL, LARGE> aux = global.cePools.take<SMALL, LARGE>();
  reformObj->copyTo(aux);
  aux->orig = Origin::REFORMBOUND;
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  assert(aux->getDegree() < static_cast<bigint>(limitAbs<SMALL, LARGE>()));
  for (Lit l : assumptions.getKeys()) {
    aux->addLhs(static_cast<SMALL>(aux->getDegree()), -l);  // bound only holds under assumptions
  }
  solver.dropExternal(lastReformUpperBound, true, deletePrevious);
  std::pair<ID, ID> res = solver.addConstraint(aux);
  lastReformUpperBound = res.second;
}

template <typename SMALL, typename LARGE>
Ce32 Optimization<SMALL, LARGE>::reduceToCardinality(const CeSuper& core) {  // does not modify core
  assert(core->hasNoZeroes());
  assert(core->hasNoUnits(solver.getLevel()));
  if (core->isClause()) {
    Ce32 result = global.cePools.take32();
    core->copyTo(result);
    return result;
  }

  CeSuper card = core->clone(global.cePools);
  // sort in decreasing coef order to minimize number of auxiliary variables, but break ties so that *small*
  // objective coefficient literals are removed first, to maximize the chances of a strong lower bound.
  card->sortInDecreasingCoefOrder(
      [&](Var v1, Var v2) { return reformObj->getCoef(card->getLit(v1)) > reformObj->getCoef(card->getLit(v2)); });
  card->simplifyToCardinality(false, card->getCardinalityDegree());

  Ce32 result = global.cePools.take32();
  card->copyTo(result);
  return result;
}

template <typename SMALL, typename LARGE>
Lit Optimization<SMALL, LARGE>::getKnapsackLit(const CePtr<SMALL, LARGE>& core) const {
  core->sortWithCoefTiebreaker([&](Var v1, Var v2) {
    const LARGE o1r2 = reformObj->getLit(v1) == core->getLit(v1) ? aux::abs(reformObj->coefs[v1] * core->coefs[v2]) : 0;
    const LARGE o2r1 = reformObj->getLit(v2) == core->getLit(v2) ? aux::abs(reformObj->coefs[v2] * core->coefs[v1]) : 0;
    return aux::sgn(o1r2 - o2r1);
    // TODO: check whether sorting the literals is a bottleneck
    // TODO: cast to LARGE when using smaller SMALL, LARGE
  });
  LARGE range = core->getDegree();
  int i = core->nVars();
  while (range >= 0 && i > 0) {
    --i;
    range -= core->nthCoef(i);
  }
  ++i;
  assert(i <= core->nVars());
  assert(i >= 0);
  return core->getLit(core->vars[i]);
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::reformObjective(const CeSuper& core) {  // modifies core
  core->weaken([&](Lit l) { return !assumptions.has(-l) && !reformObj->hasLit(l); });
  if (core->isTautology()) return State::FAIL;
  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  if (core->isUnsat()) {
    solver.addConstraint(core);
    return State::FAIL;
  }
  if (!core->hasNegativeSlack(solver.getAssumptions().getIndex())) return State::FAIL;
  core->saturate(true, false);
  Ce32 cardCore = reduceToCardinality(core);
  cardCore->orig = Origin::COREGUIDED;
  assert(cardCore->hasNoZeroes());

  // adjust the lower bound
  assert(!cardCore->empty());
  SMALL mult = 0;
  for (Var v : cardCore->getVars()) {
    if (mult == 1) break;
    if (!reformObj->hasLit(cardCore->getLit(v))) continue;  // in case of user assumption
    mult = (mult == 0) ? aux::abs(reformObj->coefs[v]) : std::min(mult, aux::abs(reformObj->coefs[v]));
  }
  if (mult == 0) return State::FAIL;  // no further literals of the objective remain

  global.stats.NCGNONCLAUSALCORES += !cardCore->isClause();

  assert(!cardCore->isTautology());
  assert(!cardCore->isUnsat());
  if (cardCore->getDegree() == cardCore->nVars()) {
    // we can just add them as unit constraints
    solver.addConstraint(cardCore);
    reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    lower_bound = std::max(lower_bound, -reformObj->getDegree());
    return State::SUCCESS;
  }
  // now we need at least 1 variable, unless the upper bound is already tight
  bool needAuxiliary = upper_bound / mult > cardCore->getDegree();
  if (needAuxiliary) {
    // add auxiliary variable
    int newN = solver.addVar(false);
    reformObj->addLhs(mult, newN);  // add only one variable for now

    // add first lazy constraint
    lazyVars.push_back(std::make_unique<LazyVar<SMALL, LARGE>>(solver, cardCore, newN, mult, upper_bound));
    lazyVars.back()->addAtLeastConstraint();
    lazyVars.back()->addAtMostConstraint();
  }
  // else the cardinality is actually an equality, and no auxiliary variables are needed.

  // reformulate the objective
  cardCore->invert();
  reformObj->addUp(cardCore, mult);
  simplifyAssumps(reformObj, assumptions);

  if (!needAuxiliary) {
    // since the cardinality is actually an equality, we can add its inverted form to the solver
    solver.addConstraint(cardCore);
  }

  lower_bound = std::max(lower_bound, -reformObj->getDegree());
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::handleInconsistency(const CeSuper& core) {  // modifies core
  assert(!core->hasNegativeSlack(solver.getLevel()));  // root inconsistency was handled by solver's learnConstraint
  assert(!core->isUnsat());

  if (toVar(assumps.back()) == boundingVar) {
    // simple bottom-up
    assert(lower_bound < boundingVal + 1);
    lower_bound = boundingVal + 1;
    return;
  }
  assert(global.options.proofAssumps);

  assert(reformObj);
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  if (lower_bound < -reformObj->getDegree()) {
    ++global.stats.NCGUNITCORES;
    lower_bound = -reformObj->getDegree();
  }

  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  core->saturate(true, false);

  if (!core->isTautology()) {
    assert(core->hasNegativeSlack(solver.getAssumptions().getIndex()));
    State result = State::SUCCESS;
    while (result == State::SUCCESS) {
      result = reformObjective(core);
      if (!global.options.optReuseCores) break;
    }
    simplifyAssumps(reformObj, assumptions);
    addReformUpperBound(false);
  }  // else only violated unit assumptions were derived

  checkLazyVariables();
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::boundObjByLastSol() {
  if (!solver.foundSolution()) throw InvalidArgument("No solution to add objective bound.");
  const LitVec& sol = solver.getLastSolution();

  upper_bound = -origObj->getRhs();
  for (Var v : origObj->getVars()) upper_bound += sol[v] > 0 ? origObj->coefs[v] : 0;

  CePtr<SMALL, LARGE> aux = global.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->orig = Origin::UPPERBOUND;
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux);
  lastUpperBound = res.second;

  if (global.options.proofAssumps) addReformUpperBound(true);
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::cloneDataIntoLS() {
  assert(presolveFirstRun);


  const rlim_t kMemoryLimit = 500000 * 1024L * 1024L; // 30 GB
  struct rlimit rl;
  rl.rlim_cur = kMemoryLimit; // 设置软限制
  rl.rlim_max = kMemoryLimit; // 设置硬限制
  if (setrlimit(9, &rl) == -1)
  {
    fprintf(stderr, "c Failed to set memory limit: %s\n", strerror(errno));
  }

  opt_dec_model = true;

  Satlike& lsSolver = solver.lsSolver;

  lsSolver.num_vars = solver.getNbVars();
  lsSolver.num_hclauses = solver.constraints.size();

  lsSolver.num_sclauses = origObj->vars.size();
  lsSolver.sumneg_min_small = 0;
  lsSolver.top_clause_weight_small = 0;
  for (const Var& v : origObj->vars) {
    int coef = origObj->coefs[v];
    if (coef > 0) {
      lsSolver.top_clause_weight_small += coef;
    } else {
      lsSolver.top_clause_weight_small += -coef;
      lsSolver.sumneg_min_small += -coef;
    }
  }
  lsSolver.top_clause_weight_small++;
  lsSolver.num_clauses = lsSolver.num_hclauses + lsSolver.num_sclauses;

  lsSolver.allocate_memory_small();
  for (int i = 0; i < lsSolver.num_clauses; i++) {
    lsSolver.clause_lit_count[i] = 0;
    lsSolver.clause_true_lit_thres_small[i] = 1;
    lsSolver.clause_lit_small[i] = nullptr;
  }

  for (int i = 1; i <= lsSolver.num_vars; i++) {
    lsSolver.var_lit_count[i] = 0;
    lsSolver.var_lit_small[i] = nullptr;
    lsSolver.var_neighbor[i] = nullptr;
  }
  lsSolver.total_soft_weight_small = 0;

  int cnt_cons = 0;
  for (const CRef& cref : solver.getRawConstraints()) {
    const Constr& constr = solver.getCA()[cref];
    const CeSuper ces = constr.toExpanded(global.cePools);
    Ce32 ce = global.cePools.take32();
    ces->copyTo(ce);
    lsSolver.clause_lit_count[cnt_cons] = ce->getVars().size();
    lsSolver.clause_lit_small[cnt_cons] = new lit_small[ce->getVars().size() + 1];
    lsSolver.clause_true_lit_thres_small[cnt_cons] = ce->getDegree();
    lsSolver.org_clause_weight_small[cnt_cons] = lsSolver.top_clause_weight_small;
    lsSolver.clause_max_weight_small[cnt_cons] = 0;
    int cnt_vars = 0;
    for (const Var& v : ce->getVars()) {
      int coef = ce->coefs[v];
      long long abs_coef = abs(coef);

      lsSolver.clause_lit_small[cnt_cons][cnt_vars].clause_num = cnt_cons;
      lsSolver.clause_lit_small[cnt_cons][cnt_vars].var_num = v;
      lsSolver.clause_lit_small[cnt_cons][cnt_vars].weight = abs_coef;

      lsSolver.avg_clause_coe_small[cnt_cons] += double(abs_coef);

      lsSolver.clause_lit_small[cnt_cons][cnt_vars].sense = (coef > 0);

      lsSolver.clause_max_weight_small[cnt_cons] = std::max(lsSolver.clause_max_weight_small[cnt_cons], abs_coef);

      lsSolver.var_lit_count[v]++;
      cnt_vars++;
    }

    lsSolver.avg_clause_coe_small[cnt_cons] = std::max(
        round(double(lsSolver.avg_clause_coe_small[cnt_cons]) / double(lsSolver.clause_lit_count[cnt_cons])), 1.0);

    lsSolver.clause_lit_small[cnt_cons][cnt_vars] = {-1, 0, false, 0};

    cnt_cons++;
  }

  for (const Var& v : origObj->vars) {
    int coef = origObj->coefs[v];
    int abs_coef = abs(coef);
    lsSolver.clause_lit_count[cnt_cons] = 1;
    lsSolver.clause_lit_small[cnt_cons] = new lit_small[lsSolver.clause_lit_count[cnt_cons] + 1];

    lsSolver.clause_lit_small[cnt_cons][0] = {cnt_cons, v, coef < 0, 1};
    lsSolver.org_clause_weight_small[cnt_cons] = abs_coef;
    lsSolver.clause_max_weight_small[cnt_cons] = 1;
    lsSolver.var_lit_count[v]++;
    lsSolver.clause_true_lit_thres_small[cnt_cons] = 1;
    lsSolver.clause_lit_small[cnt_cons][1] = {-1, 0, false, 0};
    cnt_cons++;
  }

  for (int i = 1; i <= lsSolver.num_vars; i++) {
    lsSolver.var_lit_small[i] = new lit_small[lsSolver.var_lit_count[i] + 1];
    lsSolver.var_lit_count[i] = 0;
  }

  lsSolver.num_hclauses = 0;
  lsSolver.num_sclauses = 0;
  for (int i = 0; i < lsSolver.num_clauses; i++) {
    for (int j = 0; j < lsSolver.clause_lit_count[i]; j++) {
      const Var& var = lsSolver.clause_lit_small[i][j].var_num;
      lsSolver.var_lit_small[var][lsSolver.var_lit_count[var]] = lsSolver.clause_lit_small[i][j];
      lsSolver.var_lit_count[var]++;
    }
    lsSolver.clause_visited_times[i] = 0;

    if (lsSolver.org_clause_weight_small[i] != lsSolver.top_clause_weight_small) {
      lsSolver.total_soft_weight_small += lsSolver.org_clause_weight_small[i];
      lsSolver.soft_clause_num_index[lsSolver.num_sclauses++] = i;
    } else {
      lsSolver.hard_clause_num_index[lsSolver.num_hclauses++] = i;
    }
  }

  /*

   */

  for (int i = 1; i <= lsSolver.num_vars; i++) lsSolver.var_lit_small[i][lsSolver.var_lit_count[i]].clause_num = -1;

  // TODO: rewrite SATlike::build_neighbor_relation_small() in Exact
  std::function<void()> buildNeighborData = [&lsSolver]() -> void {
    for (Var v = 1; v <= lsSolver.num_vars; v++)
      lsSolver.neighbor_flag[v] = 0;
    for (Var v = 1; v <= lsSolver.num_vars; v++) {
      lsSolver.neighbor_flag[v] = 1;
      lsSolver.var_neighbor_count[v] = 0;
      for (int i = 0; i < lsSolver.var_lit_count[v]; i++) {
        const int& c = lsSolver.var_lit_small[v][i].clause_num;
        for (int j = 0; j < lsSolver.clause_lit_count[c]; j++) {
          int nei = lsSolver.clause_lit_small[c][j].var_num;
          if (!lsSolver.neighbor_flag[nei]) {
            lsSolver.neighbor_flag[nei] = 1;
            lsSolver.temp_neighbor[lsSolver.var_neighbor_count[v]++] = nei;
          }
        }
      }

      lsSolver.neighbor_flag[v] = 0;

      lsSolver.var_neighbor[v] = new int[lsSolver.var_neighbor_count[v]];

      for (int i = 0; i < lsSolver.var_neighbor_count[v]; i++) {
        lsSolver.var_neighbor[v][i] = lsSolver.temp_neighbor[i];
        lsSolver.neighbor_flag[lsSolver.temp_neighbor[i]] = 0;
      }
    }
  };
  buildNeighborData();

  lsSolver.best_soln_feasible = 0;
  lsSolver.opt_unsat_weight_small = lsSolver.total_soft_weight_small + 1;
  lsSolver.opt_realobj_small = lsSolver.total_soft_weight_small + 1;

  //
  std::function<void(Satlike&)> print = [](Satlike& s) {
    using std::cout, std::endl;
    cout << "num_vars\n";
    cout << s.num_vars << "\n";
    cout << "num_hclauses\n";
    cout << s.num_hclauses << "\n";
    cout << "num_sclauses\n";
    cout << s.num_sclauses << "\n";
    cout << "sumneg_min_small\n";
    cout << s.sumneg_min_small << "\n";
    cout << "top_clause_weight_small\n";
    cout << s.top_clause_weight_small << "\n";
    cout << "num_clauses\n";
    cout << s.num_clauses << "\n";
    cout << "clause_lit_count\n";
    for (int i = 0; i < s.num_clauses; i++) cout << s.clause_lit_count[i] << " ";
    cout << "\n";
    cout << "clause_true_lit_thres_small\n";
    for (int i = 0; i < s.num_clauses; i++) cout << s.clause_true_lit_thres_small[i] << " ";
    cout << "\n";
    cout << "org_clause_weight_small\n";
    for (int i = 0; i < s.num_clauses; i++) cout << s.org_clause_weight_small[i] << " ";
    cout << "\n";
    cout << "clause_lit_small\n";
    for (int i = 0; i < s.num_clauses; i++) {
      for (int j = 0; j < s.clause_lit_count[i]; j++) cout << s.clause_lit_small[i][j] << " ";
      cout << "\n";
    }
    cout << "avg_clause_coe_small\n";
    for (int i = 0; i < s.num_clauses; i++) cout << s.avg_clause_coe_small[i] << " ";
    cout << "\n";
    cout << "clause_max_weight_small\n";
    for (int i = 0; i < s.num_clauses; i++) cout << s.clause_max_weight_small[i] << " ";
    cout << "\n";
    cout << "var_lit_count\n";
    for (int i = 1; i <= s.num_vars; i++) cout << s.var_lit_count[i] << " ";
    cout << "\n";
    cout << "var_lit_small\n";
    for (int i = 1; i <= s.num_vars; i++) {
      for (int j = 0; j < s.var_lit_count[i]; j++) cout << s.var_lit_small[i][j] << " ";
      cout << "\n";
    }
    cout << "clause_visited_times\n";
    for (int i = 0; i < s.num_clauses; i++) cout << s.clause_visited_times[i] << " ";
    cout << "\n";
    cout << "total_soft_weight_small\n";
    cout << s.total_soft_weight_small << "\n";
    cout << "soft_clause_num_index\n";
    for (int i = 0; i < s.num_sclauses; i++) cout << s.soft_clause_num_index[i] << " ";
    cout << "\n";
    cout << "hard_clause_num_index\n";
    for (int i = 0; i < s.num_hclauses; i++) cout << s.hard_clause_num_index[i] << " ";
    cout << "\n";
    cout << "var_neighbor_count\n";
    for (int i = 1; i <= s.num_vars; i++) cout << s.var_neighbor_count[i] << " ";
    cout << "\n";
    cout << "var_neighbor\n";
    for (int i = 1; i <= s.num_vars; i++) {
      for (int j = 0; j < s.var_neighbor_count[i]; j++) cout << s.var_neighbor[i][j] << " ";
      cout << "\n";
    }
    cout << "best_soln_feasible\n";
    cout << s.best_soln_feasible << "\n";
    cout << "opt_unsat_weight_small\n";
    cout << s.opt_unsat_weight_small << "\n";
    cout << "opt_realobj_small\n";
    cout << s.opt_realobj_small << "\n";
  };

  //print(lsSolver);

  std::cout << "Finish cloning data from SAT to LS\n";
}

template <typename SMALL, typename LARGE>
SolveState Optimization<SMALL, LARGE>::run(bool optimize, double timeout) {
  try {
    solver.presolve();  // will run only once, but also short-circuits (throws UnsatEncounter) when unsat was reached
    std::cout << solver.getNbConstraints() << " constraints\n";
    if (presolveFirstRun && !solver.isClone) {
      // TODO: clone data from PB-CDCL Solver to PB-LS Solver
      cloneDataIntoLS();
      presolveFirstRun = false;
      solver.isClone = true;
    }
  } catch (const UnsatEncounter&) {
    lower_bound = upper_bound;
    return SolveState::UNSAT;
  }
  while (true) {
    if (timeout != 0 && global.stats.getRunTime() > timeout) return SolveState::TIMEOUT;
    quit::checkInterrupt(global);
    // NOTE: it's possible that upper_bound < lower_bound, since at the point of optimality, the objective-improving
    // constraint yields UNSAT, at which case core-guided search can derive any constraint.
    StatNum current_time = global.stats.getDetTime();

    // There are three possibilities:
    // - no assumptions are set (because something happened during previous core-guided step)
    // - only the given assumptions are set (because the previous step was not core-guided)
    // - more than only the given assumptions are set (because the previous core-guided step did not finish)

    assumps.clear();
    bool topdown = false;
    if (optimize && !origObj->empty() && lower_bound < upper_bound &&
        (global.options.optRatio.get() >= 1 ||
         global.stats.DETTIMEBOTTOMUP <
             global.options.optRatio.get() * (global.stats.DETTIMETOPDOWN + global.stats.DETTIMEBOTTOMUP))) {
      // figure out and set new bottom-up assumptions
      if (global.options.optCoreguided && global.options.proofAssumps) {
        assert(reformObj);
        reformObj->removeEqualities(solver.getEqualities());
        simplifyAssumps(reformObj, assumptions);
        reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
        if (!reformObj->isSortedInDecreasingCoefOrder()) {
          reformObj->sortInDecreasingCoefOrder([](Var v1, Var v2) { return v1 < v2; });
        }
        if (reformObj->empty()) {
          solver.setAssumptions(assumptions.getKeys(), false);
        } else {
          assumps.insert(assumps.end(), assumptions.getKeys().begin(), assumptions.getKeys().end());
          VarVec& refVars = reformObj->vars;
          if (global.options.optStratification.get() == 0) {
            for (const Var v : refVars) assumps.push_back(-reformObj->getLit(v));
          } else {
            LARGE allowed =
                (upper_bound - lower_bound) - (upper_bound - lower_bound) / global.options.optStratification.get();
            assert(allowed > 0);
            SMALL lastCoef = 0;
            SMALL cf = 0;
            for (const Var v : refVars) {
              cf = aux::abs(reformObj->coefs[v]);
              if (allowed <= 0 && cf != lastCoef) break;
              assumps.push_back(-reformObj->getLit(v));
              allowed -= cf;
              lastCoef = cf;
            }
          }
          solver.setAssumptions(assumps, true);
        }
      } else {
        boundBottomUp();
        assumps.insert(assumps.end(), assumptions.getKeys().begin(), assumptions.getKeys().end());
        assumps.push_back(-boundingVar);
        solver.setAssumptions(assumps, true);
      }
    } else {  // set regular assumptions
      topdown = true;
      solver.setAssumptions(assumptions.getKeys(), false);
    }

    SolveState reply;
    if (solver.lastGlobalDual && solver.lastGlobalDual->hasNegativeSlack(solver.getAssumptions().getIndex())) {
      // NOTE: this optimization really helps with knapsack instances, because it immediately fixes a bunch of variables
      // TODO: generalize this: reformulate the *original* objective with the new bound after an inconsistency?
      reply = SolveState::INCONSISTENT;
      solver.lastCore = solver.lastGlobalDual;
    } else {
      try {
        reply = aux::timeCall<SolveState>([&] { return solver.solve(); },
                                          topdown ? global.stats.SOLVETIMETOPDOWN : global.stats.SOLVETIMEBOTTOMUP);
      } catch (const UnsatEncounter&) {
        reply = SolveState::UNSAT;
      }
      if (topdown) {
        global.stats.DETTIMETOPDOWN += global.stats.getDetTime() - current_time;
      } else {
        global.stats.DETTIMEBOTTOMUP += global.stats.getDetTime() - current_time;
      }
    }

    if (reply == SolveState::SAT) {
      assert(solver.foundSolution());
      ++global.stats.NSOLS;
      if (optimize) {
        boundObjByLastSol();
        printObjBounds(true);
      }
      solver.clearAssumptions();
      return SolveState::SAT;
    } else if (reply == SolveState::LSSAT) {
      // PBS NOT PBO!
      solver.lastSol = LitVec(solver.lsSolver.num_vars + 1);
      for (int i = 1 ; i <= solver.lsSolver.num_vars; i++) {
        solver.lastSol.value()[i] = solver.lsSolver.low_unsat_hard_small[i] > 0 ? 1 : 0;
      }
      return SolveState::LSSAT;
    } else if (reply == SolveState::INCONSISTENT) {
      assert(!solver.getAssumptions().isEmpty());
      ++global.stats.NCORES;
      if (solver.getAssumptions().size() > assumptions.size()) {
        if (solver.lastCore->falsifiedBy(assumptions)) {
          solver.clearAssumptions();
          lower_bound = upper_bound;
          return SolveState::INCONSISTENT;
        }
        current_time = global.stats.getDetTime();
        aux::timeCallVoid([&] { handleInconsistency(solver.lastCore); }, global.stats.SOLVETIMEBOTTOMUP);
        global.stats.DETTIMEBOTTOMUP += global.stats.getDetTime() - current_time;
        if (global.options.proofAssumps) addLowerBound();
        solver.clearAssumptions();
        printObjBounds(false);
      } else {
        assert(solver.getAssumptions().size() == assumptions.size());  // no bottom-up assumptions
        assert(solver.lastCore->falsifiedBy(assumptions));
        lower_bound = upper_bound;
        return SolveState::INCONSISTENT;
      }
    } else {
      assert(reply == SolveState::INPROCESSED || reply == SolveState::UNSAT);
      if (global.options.printCsvData) {
        global.stats.printCsvLine(static_cast<StatNum>(lower_bound), static_cast<StatNum>(upper_bound));
      }
      if (reply == SolveState::UNSAT) {
        lower_bound = upper_bound;
      }
      return reply;
    }
  }
}

template <typename SMALL, typename LARGE>
SolveState Optimization<SMALL, LARGE>::runFull(bool optimize, double timeout) {
  SolveState result = SolveState::INPROCESSED;
  while (result == SolveState::INPROCESSED || (result == SolveState::SAT && optimize)) {
    result = run(optimize, timeout);
  }
  return result;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::boundBottomUp() {
  assert(lower_bound < upper_bound);
  LARGE bnd = lower_bound + (global.options.optPrecision.get() == 0
                                 ? static_cast<LARGE>(0)
                                 : (upper_bound - lower_bound) / global.options.optPrecision.get());
  assert(bnd < upper_bound);
  assert(bnd >= lower_bound);
  if (boundingVar == 0 || bnd != boundingVal) {
    boundingVal = bnd;
    CeArb bound = global.cePools.takeArb();
    origObj->copyTo(bound);
    assert(bound->getDegree() == 0);
    bound->addRhs(boundingVal);  // objective must be at least middle
    bound->invert();             // objective must be at most middle
    boundingVar = solver.addVar(false);
    bound->addLhs(bound->getDegree(), boundingVar);  // ~boundingVar enables bisect constraint
    bound->orig = Origin::BOTTOMUP;
    solver.addConstraint(bound);
  }
}

template class Optimization<int, long long>;
template class Optimization<long long, int128>;
template class Optimization<int128, int128>;
template class Optimization<int128, int256>;
template class Optimization<bigint, bigint>;

template struct LazyVar<int, long long>;
template struct LazyVar<long long, int128>;
template struct LazyVar<int128, int128>;
template struct LazyVar<int128, int256>;
template struct LazyVar<bigint, bigint>;

}  // namespace xct
