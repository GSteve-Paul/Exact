/**********************************************************************
This file is part of Exact.

Copyright (c) 2022 Jo Devriendt

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

#include "IneqExpr.hpp"
#include "../ILP.hpp"
#include "Theory.hpp"
#include "auxiliary.hpp"
#include "doctest/doctest.h"

namespace fodot {

std::ostream& operator<<(std::ostream& os, const IneqTerm& t) { return os << t->getRepr(); }

IneqTerm IneqExpr::reduceFull() const {
  return flatten()->pushMinus(false).first->mergeMin().first->mergeMax().first->bigM();
}

void WeightedSum::cleanZeroes() {
  aux::erase_if(terms, [](const auto& item) { return item.second == 0; });
}

WeightedSum::WeightedSum(const std::vector<fo_int>& coefs, const std::vector<IneqTerm>& vars, const fo_int& os)
    : IneqExpr(), terms(), offset(os) {
  assert(coefs.size() == vars.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    add(coefs[i], vars[i]);
  }
}

void WeightedSum::collectDomains() const {
  for (const auto& kv : terms) {
    if (kv.second == 0) continue;
    kv.first->collectDomains();
  }
}

void WeightedSum::addTo(xct::ILP& ilp) const {
  assert(false);  // ILP addition should be managed by parent
}
void WeightedSum::addToAsTop(xct::ILP& ilp) const {
  // NOTE: only used to construct objective for now
  std::vector<bigint> coefs;
  coefs.reserve(terms.size());
  std::vector<xct::IntVar*> vars;
  vars.reserve(terms.size());
  for (const auto& kv : terms) {
    kv.first->addTo(ilp);
    vars.push_back(ilp.getVarFor(kv.first->getRepr()));
    coefs.push_back(kv.second);
  }
  ilp.setObjective(coefs, vars, {}, 1, offset);
}

const std::string WeightedSum::getRepr() const {
  return getReprLHS('+') + (offset == 0 ? "" : ((offset > 0 ? "+" : "") + std::to_string(offset)));
}

const std::string WeightedSum::getReprLHS(char connective) const {
  std::unordered_map<std::string, fo_int> reprsmap;
  reprsmap.reserve(terms.size());
  for (const auto& kv : terms) {
    const std::string r = kv.first->getRepr();
    if (reprsmap.count(r) == 0) reprsmap[r] = 0;
    reprsmap[r] += kv.second;
  }
  std::vector<std::string> reprs;
  reprs.reserve(reprsmap.size());
  for (const auto& kv : reprsmap) {
    if (kv.second == 0) continue;
    reprs.push_back((kv.second == 1 ? "" : (kv.second == -1 ? "-" : std::to_string(kv.second))) + kv.first +
                    connective);
  }
  std::sort(reprs.begin(), reprs.end());
  std::string repr = "";
  for (const std::string& r : reprs) {
    repr += r;
  }
  if (repr.size() > 0) {
    assert(repr.back() == connective);
    repr.pop_back();
  }
  return repr;
}

fo_int WeightedSum::getMin() const {
  fo_int min = offset;
  for (const auto& kv : terms) {
    min += kv.second * (kv.second > 0 ? kv.first->getMin() : kv.first->getMax());
  }
  return min;
}

fo_int WeightedSum::getMax() const {
  fo_int max = offset;
  for (const auto& kv : terms) {
    max += kv.second * (kv.second > 0 ? kv.first->getMax() : kv.first->getMin());
  }
  return max;
}

void WeightedSum::add(const fo_int& coef, const IneqTerm& it) {
  assert(it != nullptr);
  if (terms.count(it) == 0) terms[it] = 0;
  terms[it] += coef;
}

void WeightedSum::merge(const WeightedSum& other, const fo_int& factor) {
  offset += factor * other.offset;
  for (const auto& kv : other.terms) {
    add(factor * kv.second, kv.first);
  }
}

std::shared_ptr<WeightedSum> WeightedSum::flatten_() const {
  std::shared_ptr<WeightedSum> res =
      std::make_shared<WeightedSum>(std::vector<fo_int>(), std::vector<IneqTerm>(), offset);
  for (const auto& kv : terms) {
    IneqTerm child = kv.first->flatten();
    const WeightedSum* ws = dynamic_cast<const WeightedSum*>(child.get());
    if (ws) {
      res->merge(*ws, kv.second);
    } else {
      res->add(kv.second, child);
    }
  }
  return res;
}
IneqTerm WeightedSum::flatten() const { return flatten_(); }

std::pair<IneqTerm, bool> WeightedSum::mergeMin() const {
  // NOTE: should only happen at call to top weightedSum (e.g. for objective). Other calls are passed to Geq.
  std::vector<fo_int> coefs =
      xct::aux::comprehension(terms, [](const std::pair<IneqTerm, fo_int>& ti) { return ti.second; });
  std::vector<IneqTerm> vars =
      xct::aux::comprehension(terms, [](const std::pair<IneqTerm, fo_int>& ti) { return ti.first->mergeMin().first; });
  return {std::make_shared<WeightedSum>(coefs, vars, offset), false};
}

std::pair<IneqTerm, bool> WeightedSum::mergeMax() const {
  // NOTE: should only happen at call to top weightedSum (e.g. for objective). Other calls are passed to Geq.
  std::vector<fo_int> coefs =
      xct::aux::comprehension(terms, [](const std::pair<IneqTerm, fo_int>& ti) { return ti.second; });
  std::vector<IneqTerm> vars =
      xct::aux::comprehension(terms, [](const std::pair<IneqTerm, fo_int>& ti) { return ti.first->mergeMax().first; });
  return {std::make_shared<WeightedSum>(coefs, vars, offset), false};
}

std::shared_ptr<WeightedSum> WeightedSum::pushMinus_(bool minus, bool addOne) const {
  std::vector<fo_int> coefs;
  coefs.reserve(terms.size());
  std::vector<IneqTerm> vars;
  vars.reserve(terms.size());
  fo_int offs = (minus ? -offset : offset) - (int)addOne;
  for (const auto& kv : terms) {
    auto [child, state] = kv.first->pushMinus(minus == (kv.second > 0));
    vars.push_back(child);
    if (state == PushMinusState::STILLMINUS) {
      coefs.push_back(-xct::aux::abs(kv.second));
    } else {
      coefs.push_back(xct::aux::abs(kv.second));
      if (state == PushMinusState::FIXOFFSET) {
        offs -= coefs.back();
      }
    }
  }
  return std::make_shared<WeightedSum>(coefs, vars, offs);
}

std::pair<IneqTerm, PushMinusState> WeightedSum::pushMinus(bool minus) const {
  return {pushMinus_(minus, false), PushMinusState::OK};
}

IneqTerm WeightedSum::bigM() const {
  // NOTE: should only happen at call to top weightedSum (e.g. for objective). Other calls are passed to Geq.
  std::vector<fo_int> coefs =
      xct::aux::comprehension(terms, [](const std::pair<IneqTerm, fo_int>& ti) { return ti.second; });
  std::vector<IneqTerm> vars =
      xct::aux::comprehension(terms, [](const std::pair<IneqTerm, fo_int>& ti) { return ti.first->bigM(); });
  return std::make_shared<WeightedSum>(coefs, vars, offset);
}

Geq::Geq(const std::shared_ptr<const WeightedSum>& arg) : IneqExpr(), argument(arg) {}
void Geq::collectDomains() const { argument->collectDomains(); }

IneqTerm Geq::flatten() const { return std::make_shared<Geq>(argument->flatten_()); }

std::pair<IneqTerm, bool> Geq::mergeMin() const {
  if (falseIffMin()) {
    std::shared_ptr<WeightedSum> res = std::make_shared<WeightedSum>(std::vector<fo_int>(), std::vector<IneqTerm>(), 0);
    for (const auto& kv : argument->terms) {
      if (kv.second == 0) continue;
      auto [child, isMin] = kv.first->mergeMin();
      const Geq* geq = dynamic_cast<const Geq*>(child.get());
      if (isMin && geq != nullptr) {
        for (const auto& kv2 : geq->argument->terms) {
          if (kv2.second == 0) continue;
          res->add(kv2.second > 0 ? 1 : -1, kv2.first);
        }
      } else {
        res->add(kv.second > 0 ? 1 : -1, child);
      }
    }
    res->offset = -1 - res->getMin();
    return {std::make_shared<const Geq>(res), true};
  } else {
    std::shared_ptr<WeightedSum> res =
        std::make_shared<WeightedSum>(std::vector<fo_int>(), std::vector<IneqTerm>(), argument->offset);
    for (const auto& kv : argument->terms) {
      auto [child, isSelfMin] = kv.first->mergeMin();
      res->add(kv.second, child);
    }
    return {std::make_shared<Geq>(res), false};
  }
}

std::pair<IneqTerm, bool> Geq::mergeMax() const {
  if (trueIffMax()) {
    std::shared_ptr<WeightedSum> res = std::make_shared<WeightedSum>(std::vector<fo_int>(), std::vector<IneqTerm>(), 0);
    for (const auto& kv : argument->terms) {
      if (kv.second == 0) continue;
      auto [child, isMax] = kv.first->mergeMax();
      const Geq* geq = dynamic_cast<const Geq*>(child.get());
      if (isMax && geq != nullptr) {
        for (const auto& kv2 : geq->argument->terms) {
          if (kv2.second == 0) continue;
          res->add(kv2.second > 0 ? 1 : -1, kv2.first);
        }
      } else {
        res->add(kv.second > 0 ? 1 : -1, child);
      }
    }
    res->offset = -res->getMax();
    return {std::make_shared<Geq>(res), true};
  } else {
    std::shared_ptr<WeightedSum> res =
        std::make_shared<WeightedSum>(std::vector<fo_int>(), std::vector<IneqTerm>(), argument->offset);
    for (const auto& kv : argument->terms) {
      auto [child, isMax] = kv.first->mergeMax();
      res->add(kv.second, child);
    }
    return {std::make_shared<Geq>(res), false};
  }
}

void Geq::addTo(xct::ILP& ilp) const {
  if (ilp.getVarFor(getRepr())) return;
  std::vector<bigint> coefs;
  coefs.reserve(argument->terms.size());
  std::vector<xct::IntVar*> vars;
  vars.reserve(argument->terms.size());
  for (const auto& kv : argument->terms) {
    kv.first->addTo(ilp);
    vars.push_back(ilp.getVarFor(kv.first->getRepr()));
    coefs.push_back(kv.second);
  }
  assert(!ilp.getVarFor(getRepr()));  // no cycles
  xct::IntVar* head = ilp.addVar(getRepr(), 0, 1);
  ilp.addReification(head, coefs, vars, {}, -argument->offset);
}
void Geq::addToAsTop(xct::ILP& ilp) const {
  assert(!ilp.getVarFor(getRepr()));  // identical formulas should be handled by tseitinization
  std::vector<bigint> coefs;
  coefs.reserve(argument->terms.size());
  std::vector<xct::IntVar*> vars;
  vars.reserve(argument->terms.size());
  for (const auto& kv : argument->terms) {
    kv.first->addTo(ilp);
    vars.push_back(ilp.getVarFor(kv.first->getRepr()));
    coefs.push_back(kv.second);
  }
  assert(!ilp.getVarFor(getRepr()));  // no cycles
  ilp.addConstraint(coefs, vars, {}, -argument->offset);
}

const std::string Geq::getRepr() const {
  if (trueIffMax()) {
    return "and(" + argument->getReprLHS(',') + ")";
  } else if (falseIffMin()) {
    return "or(" + argument->getReprLHS(',') + ")";
  } else {
    return "(" + argument->getReprLHS('+') + ">=" + std::to_string(-argument->offset) + ")";
  }
}

fo_int Geq::getMin() const { return 0; }
fo_int Geq::getMax() const { return 1; }
bool Geq::trueIffMax() const { return argument->getMax() == 0; }
bool Geq::falseIffMin() const { return argument->getMin() == -1; }

std::pair<IneqTerm, PushMinusState> Geq::pushMinus(bool minus) const {
  return {std::make_shared<Geq>(argument->pushMinus_(minus, minus)),
          minus ? PushMinusState::FIXOFFSET : PushMinusState::OK};
}

// falseIffMin can merge with one inequality via Big-M. E.g.:
// d + [c>=0] >= L+1
// becomes:
// c + Md >= ML
// with M=-min(c), L=min(d)
//
// trueIffMax can merge with one inequality. E.g.:
// d + [c>=0] >= K+1
// becomes:
// c + Nd >= NK
// with N=max(c)+1, K=max(d)

IneqTerm Geq::bigM() const {
  bool trueMax = trueIffMax();
  bool falseMin = falseIffMin();
  std::vector<IneqTerm> newVars;
  newVars.reserve(argument->terms.size());
  std::vector<fo_int> newCoefs;
  newCoefs.reserve(argument->terms.size());
  for (const auto& kv : argument->terms) {
    newCoefs.push_back(kv.second);
    const Geq* t = dynamic_cast<const Geq*>(kv.first.get());
    newVars.push_back(t ? t->bigM() : kv.first);
  }
  if (falseMin || trueMax) {
    int smallestIdx = -1;
    std::string smallestRepr;
    for (int i = 0; i < (int)newVars.size(); ++i) {
      assert(newCoefs[i] == 1 || newCoefs[i] == -1);
      const Geq* g = dynamic_cast<const Geq*>(newVars[i].get());
      if (g) {
        assert(newCoefs[i] == 1);
        if (smallestIdx != -1) {
          assert(!smallestRepr.empty());
          const std::string repr = g->getRepr();
          if (smallestRepr > repr) {
            smallestIdx = i;
            smallestRepr = repr;
          }
        } else {
          smallestIdx = i;
          smallestRepr = g->getRepr();
        }
      }
    }
    if (smallestIdx != -1) {  // we can merge :)
      assert(newCoefs[smallestIdx] == 1);
      std::shared_ptr<const Geq> it = std::dynamic_pointer_cast<const Geq>(newVars[smallestIdx]);
      assert(it);
      xct::aux::swapErase(newCoefs, smallestIdx);
      xct::aux::swapErase(newVars, smallestIdx);
      fo_int M = falseMin ? -it->argument->getMin() : it->argument->getMax() + 1;
      for (int i = 0; i < (int)newCoefs.size(); ++i) {
        newCoefs[i] *= M;
      }
      std::shared_ptr<WeightedSum> ws = std::make_shared<WeightedSum>(newCoefs, newVars, M * (argument->offset + 1));
      ws->merge(*it->argument, 1);
      return std::make_shared<Geq>(ws);
    }
  }
  return std::make_shared<Geq>(std::make_shared<WeightedSum>(newCoefs, newVars, argument->offset));
}

Terminal::Terminal(Functor& f, const std::vector<DomEl>& args) : IneqExpr(), functor(f), arguments(args) {}
void Terminal::collectDomains() const {
  if (functor.getReturnType() == Type::STRING) {
    Tup a = arguments;
    a.pop_back();
    functor.addToDomain(a);
  } else {
    functor.addToDomain(arguments);
  }
}

Terminal::Terminal(Functor& f, const std::vector<DomEl>& args, const DomEl& out)
    : IneqExpr(), functor(f), arguments(aux::concat(args, {out})) {
  assert(f.getReturnType() == Type::STRING);
}

IneqTerm Terminal::flatten() const { return shared_from_this(); }
std::pair<IneqTerm, bool> Terminal::mergeMin() const { return {shared_from_this(), false}; }
std::pair<IneqTerm, bool> Terminal::mergeMax() const { return {shared_from_this(), false}; }
void Terminal::addTo(xct::ILP& ilp) const {
  assert(ilp.getVarFor(getRepr()));
  return;
}
void Terminal::addToAsTop(xct::ILP& ilp) const {
  assert(false);  // ILP addition should be managed by parent
}

const std::string Terminal::getRepr() const {
  bool withEquals = functor.getReturnType() == Type::STRING;
  assert((int)arguments.size() == functor.getArity() + withEquals);
  if (functor.getArity() == 0 && !withEquals) return functor.name;
  std::string repr = functor.name + "(";
  for (int i = 0; i < functor.getArity() - 1; ++i) {
    repr += toStr(arguments[i]) + ",";
  }
  if (functor.getArity() != 0) repr += toStr(arguments[functor.getArity() - 1]);
  return repr + (withEquals ? (")=" + toStr(arguments.back())) : ")");
}

fo_int Terminal::getMin() const {
  if (functor.getReturnType() == Type::INT) {
    return xct::aux::min(xct::aux::comprehension(functor.range, [](const DomEl& de) { return std::get<fo_int>(de); }));
  } else {
    return 0;
  }
}

fo_int Terminal::getMax() const {
  if (functor.getReturnType() == Type::INT) {
    return xct::aux::max(xct::aux::comprehension(functor.range, [](const DomEl& de) { return std::get<fo_int>(de); }));
  } else {
    return 1;
  }
}

std::pair<IneqTerm, PushMinusState> Terminal::pushMinus(bool minus) const {
  return {shared_from_this(), minus ? PushMinusState::STILLMINUS : PushMinusState::OK};
}

IneqTerm Terminal::bigM() const { return shared_from_this(); }

}  // namespace fodot

using namespace fodot;

TEST_CASE("falseIffMin and trueIffMax") {
  Functor f_P("P", {Type::BOOL}, {true, false});
  Functor f_Q("Q", {Type::BOOL}, {true, false});
  Term t_P = std::make_shared<Application>(f_P, std::vector<Term>());
  Term t_Q = std::make_shared<Application>(f_Q, std::vector<Term>());
  std::vector<Term> args = {t_P, t_Q};
  Term t_iff = std::make_shared<Binary>(Op::Iff, t_P, t_Q);
  IneqTerm t_iff_in = t_iff->rewrite()->pushNegation()->toIneq()->flatten();
  [[maybe_unused]] const Geq* geq = dynamic_cast<const Geq*>(t_iff_in.get());
  CHECK(geq != nullptr);
  CHECK(geq->trueIffMax());
  CHECK(!geq->falseIffMin());
  args = {t_P};
  Term t_and = std::make_shared<Nary>(Op::And, args);
  IneqTerm t_and_in = t_and->rewrite()->pushNegation()->toIneq()->flatten();
  geq = dynamic_cast<const Geq*>(t_and_in.get());
  CHECK(geq != nullptr);
  CHECK(geq->trueIffMax());
  CHECK(geq->falseIffMin());
  Functor f_g("g", {Type::INT}, {1, 2, 3});
  Functor f_h("h", {Type::INT}, {-2, -1, 0, 1, 2});
  Term t_g = std::make_shared<Application>(f_g, std::vector<Term>());
  Term t_h = std::make_shared<Application>(f_h, std::vector<Term>());
  args = {t_g, t_h};
  Term t_plus = std::make_shared<Nary>(Op::Plus, args);
  Term t_sg = std::make_shared<Binary>(Op::StrictGreater, t_plus, D(0));
  IneqTerm it_sg = t_sg->rewrite()->pushNegation()->toIneq()->flatten();
  geq = dynamic_cast<const Geq*>(it_sg.get());
  CHECK(geq != nullptr);
  CHECK(!geq->trueIffMax());
  CHECK(!geq->falseIffMin());

  it_sg = std::make_shared<Binary>(Op::StrictGreater, t_plus, D(4))->rewrite()->pushNegation()->toIneq()->flatten();
  geq = dynamic_cast<const Geq*>(it_sg.get());
  CHECK(geq != nullptr);
  CHECK(geq->trueIffMax());
  CHECK(!geq->falseIffMin());
  it_sg = std::make_shared<Binary>(Op::StrictGreater, t_plus, D(-1))->rewrite()->pushNegation()->toIneq()->flatten();
  geq = dynamic_cast<const Geq*>(it_sg.get());
  CHECK(geq != nullptr);
  CHECK(!geq->trueIffMax());
  CHECK(geq->falseIffMin());
  // TODO: tests with coefficients after introduction of ITE
}

TEST_CASE("Translate") {
  Term t_a = D("a");
  std::vector<Term> args = {};
  Functor f_P("P", {Type::INT, Type::BOOL}, {true, false});
  Functor f_C("C", {Type::INT}, {0, 1, 2, 3});
  Term t_C = std::make_shared<Application>(f_C, args);
  Term t_1 = D(3);
  args = {t_1};
  Term t_P = std::make_shared<Application>(f_P, args);
  Term t_eq2 = std::make_shared<Binary>(Op::Equals, t_C, t_1);
  Term t_iff = std::make_shared<Binary>(Op::Iff, t_P, t_eq2);

  t_iff = t_iff->rewrite();
  CHECK(t_iff->getRepr() == "and(or(P(3),not and(3>=C,C>=3)),or(and(3>=C,C>=3),not P(3)))");
  t_iff = t_iff->pushNegation();
  CHECK(t_iff->getRepr() == "and(or(P(3),or(3>C,C>3)),or(and(3>=C,C>=3),not P(3)))");
  IneqTerm ti_iff = t_iff->toIneq();
  CHECK(ti_iff->getRepr() == "and(or(-P(3)+1,and((+3+-C>=0),and(-+3,C))),or(P(3),or((-+3+C>=1),or(+3,-C))))");
  ti_iff = ti_iff->flatten();
  CHECK(ti_iff->getRepr() == "and(or(-P(3),and((-C>=-3),and(C))),or(P(3),or((C>=4),or(-C))))");
  ti_iff = ti_iff->mergeMax().first;
  CHECK(ti_iff->getRepr() == "and(or(-P(3),and((-C>=-3),C)),or(P(3),or((C>=4),or(-C))))");
  ti_iff = ti_iff->mergeMin().first;
  CHECK(ti_iff->getRepr() == "and(or((C>=4),-C,P(3)),or(-P(3),and((-C>=-3),C)))");
  // TODO: add test for larger coefficients when ITE is implemented
}

TEST_CASE("Plus") {
  Theory theo;

  Functor* f_f = theo.voc.createFunctor("f", {Type::STRING, Type::INT}, {-1, -2, 0, 1, 2});
  Functor* f_C = theo.voc.createFunctor("C", {Type::INT}, {0, 1, 2, 3});
  std::vector<Term> args = {};
  Term t_C = std::make_shared<Application>(*f_C, args);
  args = {D("a")};
  Term t_fa = std::make_shared<Application>(*f_f, args);
  args = {D("b")};
  Term t_fb = std::make_shared<Application>(*f_f, args);
  args = {D("c")};
  Term t_fc = std::make_shared<Application>(*f_f, args);

  Term t_1 = D(2);
  args = {t_fa, t_fb, t_fc, t_1};
  Term t_sum = std::make_shared<Nary>(Op::Plus, args);

  Term t_geq = std::make_shared<Binary>(Op::Greater, t_C, t_sum);
  theo.constraints.push_back(t_geq);

  t_geq = t_geq->rewrite();
  CHECK(t_geq->getRepr() == "C>=+(2,f(\"a\"),f(\"b\"),f(\"c\"))");
  t_geq = t_geq->pushNegation();
  CHECK(t_geq->getRepr() == "C>=+(2,f(\"a\"),f(\"b\"),f(\"c\"))");
  IneqTerm ti_iff = t_geq->toIneq();
  CHECK(ti_iff->getRepr() == "(-+2+f(\"a\")+f(\"b\")+f(\"c\")+C>=0)");
  ti_iff = ti_iff->flatten();
  CHECK(ti_iff->getRepr() == "(-f(\"a\")+-f(\"b\")+-f(\"c\")+C>=2)");
  ti_iff = ti_iff->mergeMax().first;
  CHECK(ti_iff->getRepr() == "(-f(\"a\")+-f(\"b\")+-f(\"c\")+C>=2)");
  ti_iff = ti_iff->mergeMin().first;
  CHECK(ti_iff->getRepr() == "(-f(\"a\")+-f(\"b\")+-f(\"c\")+C>=2)");
  ti_iff = ti_iff->bigM();
  CHECK(ti_iff->getRepr() == "(-f(\"a\")+-f(\"b\")+-f(\"c\")+C>=2)");
  // TODO: add test for larger coefficients when ITE is implemented

  xct::ILP ilp(true);

  theo.addTo(ilp);

  std::stringstream ss;
  ilp.printInput(ss);
  CHECK(ss.str() ==
        "OBJ >= 0\n"
        "-1 f(\"a\")[0,4] -1 f(\"b\")[0,4] -1 f(\"c\")[0,4] -8 [C>=+(2,f(\"a\"),f(\"b\"),f(\"c\"))] 1 C[0,3] >= -12\n");
}

TEST_CASE("PushMinus") {
  Functor p("p", {});
  Functor q("q", {});
  Functor r("r", {});
  Functor s("s", {});
  Functor t("t", {});
  Term t_p = A(p, {});
  Term t_q = A(q, {});
  Term t_r = A(r, {});
  Term t_s = A(s, {});
  Term t_t = A(t, {});
  Term t_and = O("and", {t_r, t_s, t_t});
  Term t_not = O("not", {t_and});
  Term t_or = O("or", {t_p, t_q, t_not});
  IneqTerm it_or = t_or->toIneq();
  auto [it_or2, state] = it_or->pushMinus(false);
  CHECK(state == PushMinusState::OK);
  CHECK(it_or2->getRepr() == "or(or(-r,-s,-t),p,q)");
  CHECK(it_or->reduceFull()->getRepr() == "or(-r,-s,-t,p,q)");
  CHECK(t_or->translateFull()->getRepr() == "or(-r,-s,-t,p,q)");
}

TEST_CASE("big M") {
  std::vector<DomEl> _123 = {DomEl(0), DomEl(1), DomEl(2), DomEl(3), DomEl(4)};
  Functor p("p", {});
  Functor c("c", {Type::INT}, _123);
  Functor d("d", {Type::INT}, _123);
  Term t = O("implies", A(p, {}), O(">=", A(c, {}), A(d, {})));
  IneqTerm it = t->translateFull();
  CHECK(it->getRepr() == "(-4p+-d+c>=-4)");
}

TEST_CASE("equals false") {
  Functor p("p", {});
  Term t = O("=", A(p, {}), D(false));
  IneqTerm it = t->translateFull();
  CHECK(it->getRepr() == "and(-p)");
}