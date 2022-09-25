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

#include "Expression.hpp"
#include <sstream>
#include "../ILP.hpp"
#include "IneqExpr.hpp"
#include "Theory.hpp"
#include "auxiliary.hpp"
#include "doctest/doctest.h"

namespace fodot {

std::vector<std::pair<Op, std::string>> op2repr = {
    {Op::Not, "not"}, {Op::And, "and"},          {Op::Or, "or"},      {Op::Implies, "implies"},
    {Op::Iff, "iff"}, {Op::Equals, "="},         {Op::Greater, ">="}, {Op::StrictGreater, ">"},
    {Op::Plus, "+"},  {Op::Minus, "-"},          {Op::Forall, "all"}, {Op::Exists, "any"},
    {Op::Sum, "sum"}, {Op::Alldiff, "distinct"}, {Op::Count, "count"}};

const std::string& getString(Op o) {
  for (const auto& p : op2repr)
    if (p.first == o) return p.second;
  assert(false);
  return op2repr.begin()->second;
}
Op getOp(const std::string& s) {
  for (const auto& p : op2repr)
    if (p.second == s) return p.first;
  assert(false);
  return Op::Not;
}

Type getOutType(Op o) {
  switch (o) {
    case Op::Not:
    case Op::And:
    case Op::Or:
    case Op::Implies:
    case Op::Iff:
    case Op::Equals:
    case Op::Greater:
    case Op::StrictGreater:
    case Op::Forall:
    case Op::Exists:
    case Op::Alldiff:
      return Type::BOOL;
    case Op::Plus:
    case Op::Minus:
    case Op::Sum:
    case Op::Count:
      return Type::INT;
    default:
      assert(false);
      return Type::STRING;
  }
}

bool hasInType(Op o, Type t) {
  switch (o) {
    case Op::Not:
    case Op::And:
    case Op::Or:
    case Op::Implies:
    case Op::Iff:
    case Op::Forall:
    case Op::Exists:
    case Op::Count:
      return t == Type::BOOL;
    case Op::Greater:
    case Op::StrictGreater:
    case Op::Minus:
    case Op::Sum:
      return t == Type::INT;
    case Op::Plus:
      return t == Type::INT;
    case Op::Alldiff:
      return t == Type::INT || t == Type::STRING;
    case Op::Equals:
      return true;
    default:
      assert(false);
      return false;
  }
}

bool associative(Op o) {
  switch (o) {
    case Op::Not:
    case Op::Implies:
    case Op::Greater:
    case Op::StrictGreater:
    case Op::Minus:
      return false;
    case Op::And:
    case Op::Or:
    case Op::Iff:
    case Op::Equals:
    case Op::Plus:
    case Op::Forall:
    case Op::Exists:
    case Op::Sum:
    case Op::Alldiff:
    case Op::Count:
      return true;
    default:
      assert(false);
      return false;
  }
}

std::ostream& operator<<(std::ostream& os, const Op& o) { return os << getString(o); }

Expression::Expression(Type t) : type(t) {}

std::ostream& operator<<(std::ostream& os, const std::shared_ptr<const Expression>& t) { return os << t->getRepr(); }
std::ostream& operator<<(std::ostream& os, const std::shared_ptr<const RawExpr>& t) { return os << t->getRepr(); }

Term RawExpr::reduceFull() const {
  return instantiateVars()->rewrite()->reduceJustifieds().first->pushNegation()->mergeIte();
}
IneqTerm RawExpr::translateFull(bool addAnd) const {
  if (addAnd) {
    assert(type == Type::BOOL);
    // NOTE: outer "and" ensures we get a constraint (a Geq)
    std::vector<Term> args = {reduceFull()};
    return std::make_shared<Nary>(Op::And, args)->toIneq()->reduceFull();
  } else {
    return reduceFull()->toIneq()->reduceFull();
  }
}
Term RawExpr::instantiateVars(InstVarState ivs) const {
  return instantiateVars(std::unordered_map<Var, DomEl, varhash>(), ivs);
}
void RawExpr::stripTopAnds(std::vector<Term>& out) const { out.push_back(shared_from_this()); }

std::shared_ptr<Val> D(const DomEl& de) { return std::make_shared<Val>(de); }
std::shared_ptr<Var> V(const std::string& s) { return std::make_shared<Var>(s); }
std::shared_ptr<Application> A(Functor& f, const std::initializer_list<Term>& args) {
  return std::make_shared<Application>(f, args);
}
std::shared_ptr<Application> A(Functor& f, const Term& arg1) { return A(f, {arg1}); }
std::shared_ptr<Application> A(Functor& f, const Term& arg1, const Term& arg2) { return A(f, {arg1, arg2}); }
std::shared_ptr<Application> A(Functor& f, const Term& arg1, const Term& arg2, const Term& arg3) {
  return A(f, {arg1, arg2, arg3});
}
std::shared_ptr<Application> A(Functor& f, const Term& arg1, const Term& arg2, const Term& arg3, const Term& arg4) {
  return A(f, {arg1, arg2, arg3, arg4});
}
std::shared_ptr<Operator> O(const std::string& op, const std::initializer_list<Term>& args) {
  std::vector<Term> arguments(std::begin(args), std::end(args));
  Op o;
  if (op == "<" || op == "=<") {
    checkArity(2, arguments.size(), " when parsing " + op);
    std::swap(arguments[0], arguments[1]);
    o = (op == "<" ? Op::StrictGreater : Op::Greater);
  } else {
    o = getOp(op);
  }
  if (o == Op::Not || o == Op::Minus) {
    checkArity(1, arguments.size(), " when parsing " + op);
    return std::make_shared<Unary>(o, arguments[0]);
  } else if (o == Op::And || o == Op::Or || o == Op::Plus) {
    return std::make_shared<Nary>(o, arguments);
  } else {
    checkArity(2, arguments.size(), " when parsing " + op);
    return std::make_shared<Binary>(o, arguments[0], arguments[1]);
  }
}
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1) { return O(op, {arg1}); }
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1, const Term& arg2) { return O(op, {arg1, arg2}); }
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1, const Term& arg2, const Term& arg3) {
  return O(op, {arg1, arg2, arg3});
}
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1, const Term& arg2, const Term& arg3,
                            const Term& arg4) {
  return O(op, {arg1, arg2, arg3, arg4});
}
std::shared_ptr<FirstOrder> all(const std::initializer_list<Scope>& scs, const Term& arg) {
  return std::make_shared<FirstOrder>(Op::Forall, scs, arg);
}
std::shared_ptr<FirstOrder> all(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg) {
  return all({{vs, f}}, arg);
}
std::shared_ptr<FirstOrder> any(const std::initializer_list<Scope>& scs, const Term& arg) {
  return std::make_shared<FirstOrder>(Op::Exists, scs, arg);
}
std::shared_ptr<FirstOrder> any(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg) {
  return any({{vs, f}}, arg);
}
std::shared_ptr<FirstOrder> distinct(const std::initializer_list<Scope>& scs, const Term& arg) {
  return std::make_shared<FirstOrder>(Op::Alldiff, scs, arg);
}
std::shared_ptr<FirstOrder> distinct(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg) {
  return distinct({{vs, f}}, arg);
}
std::shared_ptr<FirstOrder> sum(const std::initializer_list<Scope>& scs, const Term& arg) {
  return std::make_shared<FirstOrder>(Op::Sum, scs, arg);
}
std::shared_ptr<FirstOrder> sum(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg) {
  return sum({{vs, f}}, arg);
}
std::shared_ptr<FirstOrder> count(const std::initializer_list<Scope>& scs, const Term& arg) {
  return std::make_shared<FirstOrder>(Op::Count, scs, arg);
}
std::shared_ptr<FirstOrder> count(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg) {
  return count({{vs, f}}, arg);
}
std::shared_ptr<Ite> IE(const std::initializer_list<std::pair<Term, Term>>& condvals) {
  return std::make_shared<Ite>(condvals);
}
std::shared_ptr<Ite> IE(const Term& whentrue, const Term& cond, const Term& whenfalse) {
  return std::make_shared<Ite>(cond, whentrue, whenfalse);
}

Val::Val(const DomEl& d) : RawExpr(getType(d)), de(d) { checkType(); }
void Val::checkType() const {}
Term Val::deepCopy() const { return std::make_shared<Val>(de); }
const std::string Val::getRepr() const { return toStr(de); }
const std::vector<Term> Val::getChildren() const { return {}; }
const std::unordered_set<DomEl> Val::getRange() const { return {de}; }
IneqTerm Val::toIneq() const {
  assert(type != Type::STRING);
  fo_int v = type == Type::INT ? std::get<fo_int>(de) : (int)std::get<bool>(de);
  std::vector<fo_int> cfs = {};
  std::vector<IneqTerm> vs = {};
  return std::make_shared<WeightedSum>(cfs, vs, v);
}
Term Val::rewrite() const { return shared_from_this(); }
Term Val::pushNegation(bool neg) const {
  if (neg) {
    assert(type == Type::BOOL);
    return std::make_shared<Val>(std::get<bool>(de) ? DomEl(false) : DomEl(true));
  }
  return shared_from_this();
}
Term Val::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  return shared_from_this();
}
std::pair<Term, DomEl> Val::reduceJustifieds() const { return {shared_from_this(), de}; }
Term Val::mergeIte() const { return shared_from_this(); }

Operator::Operator(Op o) : RawExpr(getOutType(o)), symbol(o) {}

Unary::Unary(Op o, const Term& arg) : Operator(o), argument(arg) { checkType(); }
Term Unary::deepCopy() const { return std::make_shared<Unary>(symbol, argument->deepCopy()); }
void Unary::checkType() const {
  if (!hasInType(symbol, argument->type))
    throw TypeClash((std::stringstream() << symbol << " cannot accept " << argument << " with type " << argument->type
                                         << " as argument.")
                        .str());
}
const std::string Unary::getRepr() const {
  return getString(symbol) + (getString(symbol).size() > 1 ? " " : "") + argument->getRepr();
}
const std::vector<Term> Unary::getChildren() const { return {argument}; }
const std::unordered_set<DomEl> Unary::getRange() const {
  if (symbol == Op::Not) {
    return {false, true};
  }
  if (symbol == Op::Minus) {
    std::unordered_set<DomEl> result;
    for (const DomEl& de : argument->getRange()) {
      result.insert(-std::get<fo_int>(de));
    }
    return result;
  }
  assert(false);
  return {};
}
IneqTerm Unary::toIneq() const {
  assert(symbol == Op::Minus || symbol == Op::Not);
  IneqTerm it = argument->toIneq();
  std::vector<fo_int> coefs = {-1};
  std::vector<IneqTerm> vars = {it};
  return std::make_shared<WeightedSum>(coefs, vars, symbol == Op::Not ? 1 : 0);
}
Term Unary::rewrite() const { return std::make_shared<Unary>(symbol, argument->rewrite()); }
Term Unary::pushNegation(bool neg) const {
  if (symbol == Op::Not) {
    return argument->pushNegation(!neg);
  }
  assert(!neg);  // no negation on minus
  return std::make_shared<Unary>(Op::Minus, argument->pushNegation(false));
}
Term Unary::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  if (ivs == InstVarState::ATTOP) ivs = InstVarState::NOTATTOP;
  return std::make_shared<Unary>(symbol, argument->instantiateVars(var2de, ivs));
}
std::pair<Term, DomEl> Unary::reduceJustifieds() const {
  auto [t, de] = argument->reduceJustifieds();
  if (de == _unknown_) {
    assert(t != nullptr);
    return {std::make_shared<Unary>(symbol, t), _unknown_};
  }
  DomEl res;
  if (symbol == Op::Not) {
    res = de == DomEl(true) ? DomEl(false) : DomEl(true);
  } else {
    assert(symbol == Op::Minus);
    assert(std::holds_alternative<fo_int>(de));
    res = DomEl(-std::get<fo_int>(de));
  }
  return {std::make_shared<Val>(res), res};
}
Term Unary::mergeIte() const { return std::make_shared<Unary>(symbol, argument->mergeIte()); }

Binary::Binary(Op o, const Term& a1, const Term& a2) : Operator(o), arg1(a1), arg2(a2) { checkType(); }
Term Binary::deepCopy() const { return std::make_shared<Binary>(symbol, arg1->deepCopy(), arg2->deepCopy()); }
void Binary::checkType() const {
  if (!hasInType(symbol, arg1->type))
    throw TypeClash(
        (std::stringstream() << symbol << " cannot accept " << arg1 << " with type " << arg1->type << " as argument.")
            .str());
  if (arg1->type != arg2->type)
    throw TypeClash((std::stringstream() << arg1 << " and " << arg2 << " have different type.").str());
}
const std::string Binary::getRepr() const {
  std::string delim = getString(symbol).size() > 2 ? " " : "";
  std::string repr1 = arg1->getRepr();
  std::string repr2 = arg2->getRepr();
  if (associative(symbol) && repr1 > repr2) {
    std::swap(repr1, repr2);
  }
  return repr1 + delim + getString(symbol) + delim + repr2;
}
const std::vector<Term> Binary::getChildren() const { return {arg1, arg2}; }
const std::unordered_set<DomEl> Binary::getRange() const {
  assert(getOutType(symbol) == Type::BOOL);
  return {false, true};
}
IneqTerm Binary::toIneq() const {
  assert(symbol != Op::Implies);
  assert(symbol != Op::Iff);
  if (symbol == Op::Greater || symbol == Op::StrictGreater) {
    std::vector<fo_int> coefs = {1, -1};
    std::vector<IneqTerm> vars = {arg1->toIneq(), arg2->toIneq()};
    return std::make_shared<Geq>(std::make_shared<WeightedSum>(coefs, vars, symbol == Op::StrictGreater ? -1 : 0));
  }
  if (symbol == Op::Equals) {
    // TODO: with less casts? Just emulate Application::toIneq?
    assert(arg1->type == Type::STRING);
    const Application* app = dynamic_cast<const Application*>(arg1.get());
    const Val* val = dynamic_cast<const Val*>(arg2.get());
    if (app && val) {
      assert(app->getRange().count(val->de));
    } else {
      app = dynamic_cast<const Application*>(arg2.get());
      val = dynamic_cast<const Val*>(arg1.get());
      assert(app);
      assert(val);
    }
    assert(app->functor.getReturnType() == Type::STRING);
    assert(app->getRange().count(val->de));
    // NOTE: the latter only holds because of the way Binary::reduceJustifieds is implemented

    Tup tup;
    tup.reserve(app->arguments.size() + 1);
    for (const Term& t : app->arguments) {
      const Val* v = dynamic_cast<const Val*>(t.get());
      assert(v);
      tup.push_back(v->de);
    }
    tup.push_back(val->de);
    return std::make_shared<Terminal>(app->functor, tup);
  }
  assert(false);
  return nullptr;
}
Term Binary::rewrite() const {
  Term simp1 = arg1->rewrite();
  Term simp2 = arg2->rewrite();
  if (symbol == Op::Implies) {
    std::vector<Term> args = {std::make_shared<Unary>(Op::Not, simp1), simp2};
    return std::make_shared<Nary>(Op::Or, args);
  }
  if (symbol == Op::Iff || (symbol == Op::Equals && arg1->type == Type::BOOL)) {
    std::vector<Term> args1 = {std::make_shared<Unary>(Op::Not, simp1), simp2};
    std::vector<Term> args2 = {std::make_shared<Unary>(Op::Not, simp2), simp1};
    std::vector<Term> args3 = {std::make_shared<Nary>(Op::Or, args1), std::make_shared<Nary>(Op::Or, args2)};
    return std::make_shared<Nary>(Op::And, args3);
  }
  if (symbol == Op::Equals && arg1->type == Type::INT) {
    std::vector<Term> args = {std::make_shared<Binary>(Op::Greater, simp1, simp2),
                              std::make_shared<Binary>(Op::Greater, simp2, simp1)};
    return std::make_shared<Nary>(Op::And, args);
  }
  return std::make_shared<Binary>(symbol, simp1, simp2);
}
Term Binary::pushNegation(bool neg) const {
  assert(symbol != Op::Implies);  // already translated
  assert(symbol != Op::Iff);      // already translated
  Term a1 = arg1->pushNegation(false);
  Term a2 = arg2->pushNegation(false);
  if (neg) {
    if (symbol == Op::Equals) {
      assert(arg1->type == Type::STRING);  // other types already translated
      return std::make_shared<Unary>(Op::Not, std::make_shared<Binary>(symbol, a1, a2));
    } else {
      assert(symbol == Op::Greater || symbol == Op::StrictGreater);
      std::swap(a1, a2);
      return std::make_shared<Binary>((symbol == Op::Greater ? Op::StrictGreater : Op::Greater), a1, a2);
    }
  }
  return std::make_shared<Binary>(symbol, a1, a2);
}
Term Binary::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  if (ivs == InstVarState::ATTOP) ivs = InstVarState::NOTATTOP;
  return std::make_shared<Binary>(symbol, arg1->instantiateVars(var2de, ivs), arg2->instantiateVars(var2de, ivs));
}
std::pair<Term, DomEl> Binary::reduceJustifieds() const {
  assert(symbol != Op::Implies);  // already translated
  assert(symbol != Op::Iff);      // already translated
  auto [t1, de1] = arg1->reduceJustifieds();
  auto [t2, de2] = arg2->reduceJustifieds();
  DomEl res;
  if (symbol == Op::Equals && aux::disjoint(t1->getRange(), t2->getRange())) {
    // NOTE: this is not an optimization, but avoids comparing domain elements that are out of range of a functor
    // see the assert statement in Binary::toIneq
    res = DomEl(false);
    return {std::make_shared<Val>(res), res};
  }
  if (symbol == Op::Greater || symbol == Op::StrictGreater) {
    auto [min1, max1] = getExtrema(t1->getRange());
    auto [min2, max2] = getExtrema(t2->getRange());
    if (symbol == Op::StrictGreater) {
      min2 += 1;
      max2 += 1;
    }
    if (min1 >= max2) {
      res = DomEl(true);
      return {std::make_shared<Val>(res), res};
    }
    if (max1 < min2) {
      res = DomEl(false);
      return {std::make_shared<Val>(res), res};
    }
  }
  if (de1 == _unknown_ || de2 == _unknown_) {
    return {std::make_shared<Binary>(symbol, t1, t2), _unknown_};
  }
  if (symbol == Op::Equals) {
    res = de1 == de2 ? DomEl(true) : DomEl(false);
  } else if (symbol == Op::Greater || symbol == Op::StrictGreater) {
    assert(std::holds_alternative<fo_int>(de1));
    assert(std::holds_alternative<fo_int>(de2));
    res = DomEl(std::get<fo_int>(de1) >= std::get<fo_int>(de2) + static_cast<int>(symbol == Op::StrictGreater));
  } else {
    assert(false);
  }
  return {std::make_shared<Val>(res), res};
}
Term Binary::mergeIte() const { return std::make_shared<Binary>(symbol, arg1->mergeIte(), arg2->mergeIte()); }

Nary::Nary(Op o, const std::vector<Term>& args) : Operator(o), arguments(args) { checkType(); }
Term Nary::deepCopy() const {
  return std::make_shared<Nary>(symbol,
                                xct::aux::comprehension(arguments, [](const Term& t) { return t->deepCopy(); }));
}
void Nary::checkType() const {
  if (!arguments.empty()) {
    if (!hasInType(symbol, arguments[0]->type))
      throw TypeClash((std::stringstream() << symbol << " cannot accept " << arguments[0] << " with type "
                                           << arguments[0]->type << " as argument.")
                          .str());
    for (const Term& t : arguments) {
      assert(arguments[0] != nullptr);
      assert(t != nullptr);
      if (t->type != arguments[0]->type)
        throw TypeClash((std::stringstream() << t << " and " << arguments[0] << " have different type.").str());
    }
  }
}
const std::string Nary::getRepr() const {
  std::string repr = getString(symbol) + "(";
  std::vector<std::string> reprs;
  reprs.reserve(arguments.size());
  for (const Term& t : arguments) {
    reprs.push_back(t->getRepr());
  }
  if (associative(symbol)) std::sort(reprs.begin(), reprs.end());
  for (int i = 0; i < (int)reprs.size() - 1; ++i) {
    repr += reprs[i] + ",";
  }
  if (!reprs.empty()) repr += reprs.back();
  repr += ")";
  return repr;
}
const std::vector<Term> Nary::getChildren() const { return arguments; }
const std::unordered_set<DomEl> Nary::getRange() const {
  if (getOutType(symbol) == Type::BOOL) return {false, true};
  if (symbol == Op::Plus) {
    // TODO: make more efficient by only keeping track of min/max
    fo_int min = 0;
    fo_int max = 0;
    for (const Term& t : arguments) {
      if (t->type == Type::BOOL) {
        max += 1;
        continue;
      } else {
        assert(t->type == Type::INT);
        const std::vector<fo_int> trange =
            xct::aux::comprehension(t->getRange(), [](const DomEl& de) { return std::get<fo_int>(de); });
        min += xct::aux::min(trange);
        max += xct::aux::max(trange);
      }
      assert(max >= min);
    }
    std::unordered_set<DomEl> res;
    res.reserve(max - min + 1);
    for (fo_int i = min; i <= max; ++i) {
      res.insert(i);
    }
    return res;
  }
  assert(false);
  return {};
}
IneqTerm Nary::toIneq() const {
  std::vector<IneqTerm> vars = xct::aux::comprehension(arguments, [](const Term& t) { return t->toIneq(); });
  std::vector<fo_int> coefs(arguments.size(), 1);
  if (symbol == Op::Plus) {
    return std::make_shared<WeightedSum>(coefs, vars, 0);
  }
  assert(symbol == Op::Or || symbol == Op::And);
  return std::make_shared<Geq>(std::make_shared<WeightedSum>(coefs, vars, symbol == Op::Or ? -1 : -arguments.size()));
}
Term Nary::rewrite() const {
  return std::make_shared<Nary>(symbol, xct::aux::comprehension(arguments, [](const Term& t) { return t->rewrite(); }));
}
Term Nary::pushNegation(bool neg) const {
  Op s = symbol;
  if (neg) {
    assert(symbol == Op::Or || symbol == Op::And);
    s = (symbol == Op::Or ? Op::And : Op::Or);
  }
  return std::make_shared<Nary>(
      s, xct::aux::comprehension(arguments, [neg](const Term& t) { return t->pushNegation(neg); }));
}
Term Nary::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  if (ivs == InstVarState::ATTOP && symbol != Op::And) ivs = InstVarState::NOTATTOP;
  return std::make_shared<Nary>(
      symbol, xct::aux::comprehension(arguments, [&](const Term& t) { return t->instantiateVars(var2de, ivs); }));
}
std::pair<Term, DomEl> Nary::reduceJustifieds() const {
  if (symbol == Op::Or || symbol == Op::And) {
    bool fixedByTrue = symbol == Op::Or;  // otherwise fixedByFalse
    std::vector<Term> newArgs;
    newArgs.reserve(arguments.size() + 1);
    for (const Term& a : arguments) {
      auto [t, de] = a->reduceJustifieds();
      if (de == _unknown_) {
        newArgs.push_back(t);
      } else if ((de == DomEl(true)) == fixedByTrue) {
        return {t, de};
      } else {
        assert(std::holds_alternative<bool>(de));
      }
    }
    if (newArgs.empty()) {
      DomEl res = DomEl(!fixedByTrue);
      return {std::make_shared<Val>(res), res};
    } else {
      return {std::make_shared<Nary>(symbol, newArgs), _unknown_};
    }
  } else {
    assert(symbol == Op::Plus);
    fo_int constant = 0;
    std::vector<Term> newArgs;
    newArgs.reserve(arguments.size());
    for (const Term& a : arguments) {
      auto [t, de] = a->reduceJustifieds();
      if (de == _unknown_) {
        newArgs.push_back(t);
      } else {
        if (std::holds_alternative<bool>(de)) {
          constant += (int)std::get<bool>(de);
        } else {
          assert(std::holds_alternative<fo_int>(de));
          constant += std::get<fo_int>(de);
        }
      }
    }
    DomEl c = DomEl(constant);
    if (newArgs.empty()) {
      return {std::make_shared<Val>(c), c};
    } else {
      if (constant != 0) newArgs.push_back(std::make_shared<Val>(c));
      return {std::make_shared<Nary>(Op::Plus, newArgs), _unknown_};
    }
  }
}
void Nary::stripTopAnds(std::vector<Term>& out) const {
  if (symbol == Op::And) {
    for (const Term& t : arguments) t->stripTopAnds(out);
  } else {
    out.push_back(shared_from_this());
  }
}
Term Nary::mergeIte() const {
  return std::make_shared<Nary>(symbol,
                                xct::aux::comprehension(arguments, [](const Term& t) { return t->mergeIte(); }));
}

Ite::Ite(const std::vector<std::pair<Term, Term>>& cvs) : RawExpr(cvs[0].second->type), condvals(cvs) { checkType(); }
Ite::Ite(const Term& c, const Term& t, const Term& f) : Ite({{c, t}, {std::make_shared<Unary>(Op::Not, c), f}}) {}
Ite::Ite(const Term& c)
    : Ite({{c, std::make_shared<Val>(1)}, {std::make_shared<Unary>(Op::Not, c), std::make_shared<Val>(0)}}) {}
Term Ite::deepCopy() const {
  return std::make_shared<Ite>(xct::aux::comprehension(condvals, [](const std::pair<Term, Term>& tt) {
    return std::make_pair<Term, Term>(tt.first->deepCopy(), tt.second->deepCopy());
  }));
}
void Ite::checkType() const {
  for (const auto& tt : condvals) {
    if (tt.first->type != Type::BOOL) {
      throw TypeClash((std::stringstream() << tt.first << " does not have Boolean type.").str());
    }
    if (tt.second->type != type) {
      throw TypeClash(
          (std::stringstream() << condvals[0].first << " and " << tt.second << " have different type.").str());
    }
  }
}
const std::string Ite::getRepr() const {
  assert(!condvals.empty());
  std::string res = "(";
  for (const auto& tt : condvals) {
    res += tt.second->getRepr() + " if " + tt.first->getRepr() + ", ";
  }
  res.pop_back();
  res.pop_back();
  res.push_back(')');
  return res;
}
const std::vector<Term> Ite::getChildren() const {
  std::vector<Term> res;
  res.reserve(condvals.size() * 2);
  for (const auto& tt : condvals) {
    res.push_back(tt.first);
    res.push_back(tt.second);
  }
  return res;
}
const std::unordered_set<DomEl> Ite::getRange() const {
  if (type == Type::INT) {
    auto [min, max] = getExtrema(condvals[0].second->getRange());
    for (const auto& tt : condvals) {
      auto [min2, max2] = getExtrema(tt.second->getRange());
      min = std::min(min, min2);
      max = std::max(max, max2);
    }
    std::unordered_set<DomEl> res;
    res.reserve(max - min + 1);
    for (fo_int i = min; i <= max; ++i) {
      res.insert(i);
    }
    return res;
  } else {
    std::unordered_set<DomEl> res;
    for (const auto& tt : condvals) {
      for (const DomEl& de : tt.second->getRange()) {
        res.insert(de);
      }
    }
    return res;
  }
}
IneqTerm Ite::toIneq() const {
  assert(type == Type::INT);
  std::vector<fo_int> coefs;
  coefs.reserve(condvals.size());
  std::vector<IneqTerm> vars;
  vars.reserve(condvals.size());
  for (const auto& tt : condvals) {
    const Val* v = dynamic_cast<const Val*>(tt.second.get());
    assert(v);
    if (v->de == DomEl(0)) continue;
    coefs.push_back(std::get<fo_int>(v->de));
    vars.push_back(tt.first->toIneq());
  }
  return std::make_shared<WeightedSum>(coefs, vars, 0);
}
Term Ite::rewrite() const {
  return std::make_shared<Ite>(xct::aux::comprehension(condvals, [](const std::pair<Term, Term>& tt) {
    return std::make_pair<Term, Term>(tt.first->rewrite(), tt.second->rewrite());
  }));
}
Term Ite::pushNegation(bool neg) const {
  assert(neg == false || type == Type::BOOL);
  return std::make_shared<Ite>(xct::aux::comprehension(condvals, [neg](const std::pair<Term, Term>& tt) {
    return std::make_pair<Term, Term>(tt.first->pushNegation(neg), tt.second->pushNegation());
  }));
}
Term Ite::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  if (ivs == InstVarState::ATTOP) ivs = InstVarState::NOTATTOP;
  return std::make_shared<Ite>(xct::aux::comprehension(condvals, [var2de, ivs](const std::pair<Term, Term>& tt) {
    return std::make_pair<Term, Term>(tt.first->instantiateVars(var2de, ivs), tt.second->instantiateVars(var2de, ivs));
  }));
}
std::pair<Term, DomEl> Ite::reduceJustifieds() const {
  assert(!condvals.empty());
  std::vector<std::pair<Term, Term>> reduceds;
  reduceds.reserve(condvals.size());
  for (const auto& tt : condvals) {
    const auto [t, de] = tt.first->reduceJustifieds();
    if (de == DomEl(false)) continue;
    const std::pair<Term, DomEl> td = tt.second->reduceJustifieds();
    if (de == DomEl(true)) return td;
    reduceds.push_back({t, td.first});
  }
  bool allsame = true;
  for (const auto& tt : reduceds) {
    if (reduceds[0].second->getRepr() != tt.second->getRepr()) {
      allsame = false;
      break;
    }
  }
  if (allsame) {
    Term res = reduceds[0].second;
    const Val* v = dynamic_cast<const Val*>(res.get());
    return {res, v ? v->de : _unknown_};
  }
  return {std::make_shared<Ite>(reduceds), _unknown_};
}
Term Ite::mergeIte() const {
  std::vector<std::pair<Term, Term>> mergeds;
  mergeds.reserve(condvals.size());
  for (const auto& tt : condvals) {
    Term cond = tt.first->mergeIte();
    Term val = tt.second->mergeIte();
    const Ite* v = dynamic_cast<const Ite*>(val.get());
    if (v) {
      for (const auto& tt2 : v->condvals) {
        std::vector<Term> mergedConds = {cond, tt2.first};
        mergeds.push_back({std::make_shared<Nary>(Op::And, mergedConds)->reduceJustifieds().first, tt2.second});
      }
    } else {
      mergeds.push_back({cond, val});
    }
    // TODO: what happens when condition is Ite ?
  }
  return std::make_shared<Ite>(mergeds);
}

Application::Application(Functor& f, const std::vector<Term>& args)
    : RawExpr(f.getReturnType()), functor(f), arguments(args) {
  checkType();
}
Term Application::deepCopy() const {
  return std::make_shared<Application>(functor,
                                       xct::aux::comprehension(arguments, [](const Term& t) { return t->deepCopy(); }));
}
void Application::checkType() const {
  checkArity(functor.getArity(), arguments.size(), " when parsing " + getRepr());
  if ((int)arguments.size() != functor.getArity()) throw ArityMismatch(functor.getArity(), arguments.size());
  for (int i = 0; i < (int)arguments.size(); ++i) {
    if (arguments[i]->type != functor.types[i])
      throw TypeClash((std::stringstream()
                       << "Incorrect type of " << arguments[i] << " with type " << arguments[i]->type << " as argument "
                       << i << " for functor " << functor.name << ".")
                          .str());
  }
}
const std::string Application::getRepr() const {
  if (functor.getArity() == 0) return functor.name;
  std::string repr = functor.name + "(";
  for (int i = 0; i < (int)arguments.size() - 1; ++i) {
    repr += arguments[i]->getRepr() + ",";
  }
  if (!arguments.empty()) repr += arguments.back()->getRepr();
  repr += ")";
  return repr;
}
const std::vector<Term> Application::getChildren() const { return arguments; }
const std::unordered_set<DomEl> Application::getRange() const { return functor.range; }
IneqTerm Application::toIneq() const {
  Tup tup;
  tup.reserve(arguments.size() + (functor.getReturnType() == Type::STRING ? 1 : 0));
  for (const Term& t : arguments) {
    const Val* v = dynamic_cast<const Val*>(t.get());
    assert(v);
    tup.push_back(v->de);
  }
  return std::make_shared<Terminal>(functor, tup);
}
Term Application::rewrite() const {
  return std::make_shared<Application>(functor,
                                       xct::aux::comprehension(arguments, [](const Term& t) { return t->rewrite(); }));
}
Term Application::pushNegation(bool neg) const {
  return neg ? std::make_shared<Unary>(Op::Not, shared_from_this()) : shared_from_this();
}
Term Application::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  if (ivs == InstVarState::ATTOP) ivs = InstVarState::NOTATTOP;
  return std::make_shared<Application>(
      functor, xct::aux::comprehension(arguments, [&](const Term& t) { return t->instantiateVars(var2de, ivs); }));
}
std::pair<Term, DomEl> Application::reduceJustifieds() const {
  // TODO: look at possible range for given argument ranges. If it is size 1, we can return it.
  Tup tup;
  std::vector<Term> newArgs;
  tup.reserve(arguments.size());
  newArgs.reserve(arguments.size());
  bool allknown = true;
  for (const Term& a : arguments) {
    auto [t, de] = a->reduceJustifieds();
    tup.push_back(de);
    newArgs.push_back(t);
    allknown = allknown && (de != _unknown_);
  }
  if (allknown) {
    DomEl res = functor.getInter(tup);
    if (res != _unknown_) return {std::make_shared<Val>(res), res};
  }
  return {std::make_shared<Application>(functor, newArgs), _unknown_};
}
Term Application::mergeIte() const {
  return std::make_shared<Application>(functor,
                                       xct::aux::comprehension(arguments, [](const Term& t) { return t->mergeIte(); }));
}

Var::Var(const std::string n) : RawExpr(Type::UNKN), name(n) { checkType(); }
size_t varhash::operator()(const Var& v) const { return std::hash<std::string>{}(v.name); }
bool Var::operator==(const Var& other) const { return type == other.type && name == other.name; }
std::ostream& operator<<(std::ostream& os, const Var& v) { return os << v.getRepr(); }
const std::string Var::getRepr() const { return name; }
Term Var::deepCopy() const { return std::make_shared<Var>(name); }
void Var::checkType() const {}
const std::vector<Term> Var::getChildren() const { return {}; }
const std::unordered_set<DomEl> Var::getRange() const {
  assert(false);  // should be eliminated
  return {};
}
IneqTerm Var::toIneq() const {
  assert(false);
  return nullptr;  // should be eliminated
}
Term Var::rewrite() const { return shared_from_this(); }
Term Var::pushNegation(bool neg) const {
  if (neg) {
    assert(type == Type::BOOL);
    return std::make_shared<Unary>(Op::Not, shared_from_this());
  } else {
    return shared_from_this();
  }
}
Term Var::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  if (var2de.count(*this)) {
    return std::make_shared<Val>(var2de.at(*this));
  } else {
    if (ivs == InstVarState::ALL) throw NotScoped(*this);
    return shared_from_this();
  }
}
std::pair<Term, DomEl> Var::reduceJustifieds() const {
  assert(false);
  return {shared_from_this(), _unknown_};
}
Term Var::mergeIte() const { return shared_from_this(); }

void Scope::checkInvariants() const {
  if (!range.empty()) checkArity(range[0].size(), vars.size(), " when parsing scope");
  for (int i = 0; i < (int)vars.size(); ++i) {
    for (int j = i + 1; j < (int)vars.size(); ++j) {
      if (vars[i] == vars[j]) throw std::invalid_argument("Identical variables " + vars[i] + " in scope.");
    }
  }
}
Scope::Scope(const std::vector<std::string>& vs, const Functor& f)
    : vars(vs), range(f.getInterAsRange()), rangename(f.name){};
Scope::Scope(const std::vector<std::string>& vs, const std::vector<Tup>& r, const std::string& rn)
    : vars(vs), range(r), rangename(rn) {}

FirstOrder::FirstOrder(Op o, const std::vector<Scope>& scs, const Term& arg) : Operator(o), scopes(scs), argument(arg) {
  checkType();
}
const std::string FirstOrder::getRepr() const {
  std::string res = getString(symbol) + "(" + argument->getRepr() + " for ";
  for (const Scope& sc : scopes) {  // TODO: Scope::getRepr()?
    for (const std::string& v : sc.vars) res += v + " ";
    res += "in " + sc.rangename + ", ";
  }
  res.pop_back();
  res.pop_back();
  res.push_back(')');
  return res;
}
Term FirstOrder::deepCopy() const { return std::make_shared<FirstOrder>(symbol, scopes, argument->deepCopy()); }
void FirstOrder::checkType() const {
  if (!hasInType(symbol, argument->type))
    throw TypeClash((std::stringstream() << symbol << " cannot accept " << argument << " with type " << argument->type
                                         << " as argument.")
                        .str());
  for (const Scope& sc : scopes) sc.checkInvariants();
}
const std::vector<Term> FirstOrder::getChildren() const { return {argument}; }
const std::unordered_set<DomEl> FirstOrder::getRange() const {
  assert(symbol == Op::Forall || symbol == Op::Exists || symbol == Op::Sum || symbol == Op::Count ||
         symbol == Op::Alldiff);
  if (symbol == Op::Forall || symbol == Op::Exists || symbol == Op::Alldiff) {
    return {true, false};
  }
  if (symbol == Op::Count) {
    std::unordered_set<DomEl> res;
    fo_int n = 1;
    for (const Scope& sc : scopes) n *= sc.range.size();
    res.reserve(n + 1);
    for (fo_int i = 0; i <= n; ++i) res.insert(i);
    return res;
  }
  if (symbol == Op::Sum) {
    std::unordered_set<DomEl> res = argument->getRange();
    auto [min, max] = getExtrema(res);
    fo_int n = 1;
    for (const Scope& sc : scopes) n *= sc.range.size();
    res.clear();
    res.reserve(max * n - min * n + 1);
    for (fo_int i = min * n; i <= max * n; ++i) res.insert(i);
    return res;
  }
  assert(false);
  return {};
}
IneqTerm FirstOrder::toIneq() const {
  assert(false);
  return nullptr;
}
Term FirstOrder::rewrite() const {
  assert(false);
  return nullptr;
}
Term FirstOrder::pushNegation(bool neg) const {
  assert(false);
  return nullptr;
}
Term FirstOrder::instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const {
  assert(symbol == Op::Forall || symbol == Op::Exists || symbol == Op::Sum || symbol == Op::Count ||
         symbol == Op::Alldiff);
  std::unordered_map<Var, DomEl, varhash> newvar2de = var2de;
  if (ivs == InstVarState::ATTOP && symbol != Op::Forall) ivs = InstVarState::NOTATTOP;
  if (ivs == InstVarState::NOTATTOP) {
    for (const Scope& sc : scopes) {
      for (const std::string& v : sc.vars) newvar2de.erase(Var(v));  // avoid shadowed variables to be instantiated
    }
    return std::make_shared<FirstOrder>(symbol, scopes, argument->instantiateVars(newvar2de, ivs));
  }
  assert(ivs == InstVarState::ALL || (symbol == Op::Forall && ivs == InstVarState::ATTOP));
  std::vector<Term> instantiations;
  std::vector<Var> varsToInstantiate;
  std::vector<Tup> tupcombos = {{}};
  for (const Scope& sc : scopes) {
    for (const std::string& v : sc.vars) varsToInstantiate.push_back(Var(v));
    aux::addCombinations(tupcombos, sc.range, [](const Tup& t1, const Tup& t2) {
      Tup res = t1;
      res.insert(res.end(), t2.begin(), t2.end());
      return res;
    });
  }
  for (const Tup& tup : tupcombos) {
    assert(tup.size() == varsToInstantiate.size());
    for (int i = 0; i < (int)tup.size(); ++i) {
      newvar2de[varsToInstantiate[i]] = tup[i];
    }
    instantiations.push_back(argument->instantiateVars(newvar2de, ivs));
  }
  if (symbol == Op::Count) {
    for (int i = 0; i < (int)instantiations.size(); ++i) {
      instantiations[i] = std::make_shared<Ite>(instantiations[i]);
    }
  }
  Op symb = symbol == Op::Forall ? Op::And : (symbol == Op::Exists ? Op::Or : Op::Plus);
  if (symbol == Op::Alldiff) {
    // !y in range(f): 1 >= #{x:f(x)=y}.
    const std::unordered_set<DomEl>& range = argument->getRange();
    std::vector<Term> amos;
    amos.reserve(range.size());
    std::vector<Term> equalities;
    equalities.reserve(instantiations.size() * range.size());
    for (const DomEl& de : range) {
      equalities.clear();
      Term val = D(de);
      for (const Term& t : instantiations) {
        equalities.push_back(std::make_shared<Ite>(std::make_shared<Binary>(Op::Equals, t, val)));
      }
      amos.push_back(std::make_shared<Binary>(Op::Greater, D(1), std::make_shared<Nary>(Op::Plus, equalities)));
    }
    return std::make_shared<Nary>(Op::And, amos);
  } else {
    return std::make_shared<Nary>(symb, instantiations);
  }
}
std::pair<Term, DomEl> FirstOrder::reduceJustifieds() const {
  assert(false);
  return {nullptr, _unknown_};
}
Term FirstOrder::mergeIte() const {
  assert(false);
  return nullptr;
}

}  // namespace fodot

using namespace fodot;

TEST_CASE("Simple Expression ostream check") {
  Functor f_P("P", {Type::STRING, Type::BOOL}, {true, false});
  Term t_a = D("a");
  std::vector<Term> args = {t_a};
  Term t_Pa = std::make_shared<Application>(f_P, args);
  Term t_notPa = std::make_shared<Unary>(Op::Not, t_Pa);
  args = {t_Pa, t_notPa};
  Term t_or = std::make_shared<Nary>(Op::Or, args);
  Term t_notor = std::make_shared<Unary>(Op::Not, t_or);
  std::stringstream ss;
  ss << t_notor;
  CHECK(ss.str() == "not or(P(\"a\"),not P(\"a\"))");
}

TEST_CASE("Simple Expression ostream check") {
  Functor f_P("P", {Type::STRING, Type::BOOL}, {true, false});
  Term t_a = D("a");
  std::vector<Term> args = {t_a};
  Term t_Pa = std::make_shared<Application>(f_P, args);
  Term t_notPa = std::make_shared<Unary>(Op::Not, t_Pa);
  args = {t_Pa, t_notPa};
  Term t_or = std::make_shared<Nary>(Op::Or, args);
  Term t_notor = std::make_shared<Unary>(Op::Not, t_or);
  CHECK(t_notor->getRepr() == "not or(P(\"a\"),not P(\"a\"))");
}

TEST_CASE("Test Expression type checks") {
  Functor f_P("P", {Type::INT, Type::BOOL}, {true, false});
  Term t_a = D("a");
  std::vector<Term> args = {t_a};
  CHECK_THROWS_AS(std::make_shared<Application>(f_P, args), const TypeClash&);
  Term t_1 = D(1);
  args = {t_1, t_1};
  CHECK_THROWS_AS(std::make_shared<Application>(f_P, args), const ArityMismatch&);
  args = {t_1};
  Term t_P1 = std::make_shared<Application>(f_P, args);
  CHECK_THROWS_AS(std::make_shared<Unary>(Op::Not, t_1), const TypeClash&);
  Term t_notP1 = std::make_shared<Unary>(Op::Not, t_P1);
  CHECK_THROWS_AS(std::make_shared<Binary>(Op::Implies, t_1, t_notP1), const TypeClash&);
  CHECK_THROWS_AS(std::make_shared<Binary>(Op::Iff, t_P1, t_a), const TypeClash&);
  args = {t_P1, t_notP1, t_a};
  CHECK_THROWS_AS(std::make_shared<Nary>(Op::And, args), const TypeClash&);
  args = {t_1, t_notP1};
  CHECK_THROWS_AS(std::make_shared<Nary>(Op::Or, args), const TypeClash&);
}

TEST_CASE("Test associativity") {
  std::vector<Term> args;
  Term t_a = D("a");
  Term t_b = D("b");
  Term t_aisb = std::make_shared<Binary>(Op::Equals, t_a, t_b);
  Term t_bisa = std::make_shared<Binary>(Op::Equals, t_b, t_a);
  CHECK(t_aisb->getRepr() == t_bisa->getRepr());
  Term t_1 = D(true);
  args = {t_bisa, t_1, t_bisa};
  Term t_or1 = std::make_shared<Nary>(Op::Or, args);
  args = {t_1, t_bisa, t_bisa};
  Term t_or2 = std::make_shared<Nary>(Op::Or, args);
  CHECK(t_or1->getRepr() == t_or2->getRepr());
  args = {t_1, t_1, t_1};
  Term t_or3 = std::make_shared<Nary>(Op::Or, args);
  CHECK(t_or2->getRepr() != t_or3->getRepr());
}

TEST_CASE("Rewrite") {
  Functor f_P("P", {Type::BOOL}, {true, false});
  Functor f_Q("Q", {Type::BOOL}, {true, false});
  Term t_P = std::make_shared<Application>(f_P, std::vector<Term>());
  Term t_Q = std::make_shared<Application>(f_Q, std::vector<Term>());
  std::vector<Term> args = {t_P, t_Q};
  Term t_eq = std::make_shared<Binary>(Op::Equals, t_P, t_Q);
  Term t_iff = std::make_shared<Binary>(Op::Iff, t_P, t_Q);
  Term t_eq_trans = t_eq->rewrite();
  Term t_iff_trans = t_iff->rewrite();
  CHECK(t_eq_trans->getRepr() == "and(or(P,not Q),or(Q,not P))");
  CHECK(t_eq_trans->getRepr() == t_iff_trans->getRepr());
}

TEST_CASE("Forall, exists, sum") {
  std::vector<DomEl> abc = {DomEl("a"), DomEl("b"), DomEl("c")};
  std::vector<DomEl> _123 = {DomEl(1), DomEl(2), DomEl(3)};

  Functor p("P", {Type::STRING, Type::INT, Type::BOOL}, {true, false});
  Functor q("Q", {Type::STRING, Type::BOOL}, {true, false});
  p.setDefault(false);
  q.setDefault(false);
  p.setInter({"a", 1}, true);
  p.setInter({"b", 2}, true);
  p.setInter({"c", 3}, true);
  p.setInter({"a", 2}, false);
  q.setInter({"d"}, true);
  q.setInter({"e"}, true);
  q.setInter({"f"}, false);

  std::vector<Term> vars = {std::make_shared<Var>("x"), std::make_shared<Var>("y")};

  Functor f("F", {Type::STRING, Type::INT}, _123);
  Functor r("R", {Type::STRING, Type::INT, Type::BOOL}, {true, false});

  Term t_r = std::make_shared<Application>(r, vars);
  Term t_r_fa = all({"x", "y"}, p, t_r);
  CHECK(t_r_fa->getRepr() == "all(R(x,y) for x y in P)");
  t_r_fa = t_r_fa->instantiateVars();
  CHECK(t_r_fa->getRepr() == "and(R(\"a\",1),R(\"b\",2),R(\"c\",3))");

  std::vector<Term> vars3 = vars;
  vars3.pop_back();
  Term t_f = std::make_shared<Application>(f, vars3);
  Term t_sum = sum({"x"}, q, t_f);
  Term t_sg = std::make_shared<Binary>(Op::StrictGreater, t_sum, D(3));
  std::vector<Term> args = {t_r, t_sg};
  Term t_and = std::make_shared<Nary>(Op::And, args);
  Term t_exists = any({"x", "y"}, p, t_and);

  CHECK(t_exists->getRepr() == "any(and(R(x,y),sum(F(x) for x in Q)>3) for x y in P)");
  Term grounded = t_exists->instantiateVars();
  CHECK(grounded->getRepr() ==
        "or(and(+(F(\"d\"),F(\"e\"))>3,R(\"a\",1)),and(+(F(\"d\"),F(\"e\"))>3,R(\"b\",2)),and(+(F(\"d\"),F(\"e\"))>3,R("
        "\"c\",3)))");
}

TEST_CASE("reduce justifieds") {
  std::vector<DomEl> _abc = {DomEl("a"), DomEl("b"), DomEl("c")};
  std::vector<DomEl> _123 = {DomEl(1), DomEl(2), DomEl(3)};
  Functor p("P", {});
  Functor q("Q", {Type::STRING});
  Functor c("c", {Type::INT}, _123);
  Functor d("d", {Type::INT}, _123);
  Functor f("f", {Type::INT, Type::INT, Type::STRING}, _abc);

  std::vector<Term> args;
  Term t_p = std::make_shared<Application>(p, args);
  Term t_c = std::make_shared<Application>(c, args);
  Term t_d = std::make_shared<Application>(d, args);
  args = {t_c, t_d};
  Term t_f = std::make_shared<Application>(f, args);
  args = {t_f};
  Term t_q = std::make_shared<Application>(q, args);
  Term t_minus = std::make_shared<Unary>(Op::Minus, t_d);
  Term t_eq = std::make_shared<Binary>(Op::Equals, t_minus, D(1));
  Term t_not = O("not", {t_q});
  Term t_sum = O("+", {t_c, t_d});
  Term t_sg = O(">=", {t_sum, t_c});
  Term t_and = O("and", {t_sg, t_not});
  Term t_or = O("or", {t_p, t_eq, t_and});
  CHECK(t_or->getRepr() == "or(-d=1,P,and(+(c,d)>=c,not Q(f(c,d))))");

  auto [simp, de] = t_or->reduceJustifieds();
  CHECK(de == _unknown_);
  CHECK(simp->getRepr() == "or(P,and(+(c,d)>=c,not Q(f(c,d))))");
  auto [simp5, de5] = t_or->rewrite()->reduceJustifieds();
  CHECK(simp->getRepr() == simp5->getRepr());
  d.setInter({}, 1);
  auto [simp2, de2] = t_or->reduceJustifieds();
  CHECK(de2 == _unknown_);
  CHECK(simp2->getRepr() == "or(P,and(+(1,c)>=c,not Q(f(c,1))))");
  c.setInter({}, 2);
  f.setInter({2, 1}, "a");
  q.setInter({"a"}, false);
  auto [simp3, de3] = t_or->reduceJustifieds();
  CHECK(simp3->getRepr() == "true");
  CHECK(de3 == DomEl(true));
  auto [simp4, de4] = t_or->rewrite()->reduceJustifieds();
  CHECK(simp4->getRepr() == "true");
  CHECK(de4 == DomEl(true));
}

TEST_CASE("Cardinality") {
  std::vector<DomEl> abc = {DomEl("a"), DomEl("b"), DomEl("c")};

  Functor q("Q", {Type::STRING, Type::BOOL}, {true, false});
  q.setDefault(false);
  q.setInter({"d"}, true);
  q.setInter({"e"}, true);
  q.setInter({"f"}, false);

  Var x("x");
  Term t_x = V("x");

  Functor f("phi", {Type::STRING, Type::BOOL}, {true, false});

  Term t_f = A(f, {t_x});
  Term t_count = count({"x"}, q, t_f);
  CHECK(t_count->getRepr() == "count(phi(x) for x in Q)");
  CHECK(t_count->instantiateVars()->getRepr() ==
        "+((1 if phi(\"d\"), 0 if not phi(\"d\")),(1 if phi(\"e\"), 0 if not phi(\"e\")))");
  Term t_or_alt = O(">", {t_count, D(0)});
  CHECK(t_or_alt->translateFull()->getRepr() == "or(phi(\"d\"),phi(\"e\"))");
}

TEST_CASE("Distinct") {
  Theory theo;
  std::vector<DomEl> pigeons = {DomEl("p1"), DomEl("p2"), DomEl("p3"), DomEl("p4")};
  std::vector<DomEl> holes = {DomEl("h1"), DomEl("h2"), DomEl("h3")};

  Functor* r = theo.voc.createFunctor("pigeon", {Type::STRING, Type::BOOL}, {true, false});
  r->setInterUnary(pigeons, true);
  r->setDefault(false);
  Functor* in = theo.voc.createFunctor("hole", {Type::STRING, Type::STRING}, holes);

  Var x("p");
  Term t_p = V("p");
  Term t_in = A(*in, {t_p});
  Term t_unique = distinct({"p"}, *r, t_in);

  CHECK(t_unique->getRepr() == "distinct(hole(p) for p in pigeon)");
  CHECK(
      t_unique->instantiateVars()->getRepr() ==
      "and(1>=+((1 if \"h1\"=hole(\"p1\"), 0 if not \"h1\"=hole(\"p1\")),(1 if \"h1\"=hole(\"p2\"), 0 if not "
      "\"h1\"=hole(\"p2\")),(1 if \"h1\"=hole(\"p3\"), 0 if not \"h1\"=hole(\"p3\")),(1 if \"h1\"=hole(\"p4\"), 0 if "
      "not \"h1\"=hole(\"p4\"))),1>=+((1 if \"h2\"=hole(\"p1\"), 0 if not \"h2\"=hole(\"p1\")),(1 if "
      "\"h2\"=hole(\"p2\"), 0 if not \"h2\"=hole(\"p2\")),(1 if \"h2\"=hole(\"p3\"), 0 if not \"h2\"=hole(\"p3\")),(1 "
      "if \"h2\"=hole(\"p4\"), 0 if not \"h2\"=hole(\"p4\"))),1>=+((1 if \"h3\"=hole(\"p1\"), 0 if not "
      "\"h3\"=hole(\"p1\")),(1 if \"h3\"=hole(\"p2\"), 0 if not \"h3\"=hole(\"p2\")),(1 if \"h3\"=hole(\"p3\"), 0 if "
      "not \"h3\"=hole(\"p3\")),(1 if \"h3\"=hole(\"p4\"), 0 if not \"h3\"=hole(\"p4\"))))");

  theo.constraints.push_back(t_unique);

  xct::ILP ilp(true);
  theo.addTo(ilp);

  std::stringstream ss;
  ilp.printInput(ss);
  CHECK(
      ss.str() ==
      "OBJ >= 0\n"
      "(-hole(\"p1\")=\"h2\"+-hole(\"p2\")=\"h2\"+-hole(\"p3\")=\"h2\"+-hole(\"p4\")=\"h2\">=-1) <=> -1 "
      "hole(\"p1\")=\"h2\" -1 hole(\"p2\")=\"h2\" -1 hole(\"p3\")=\"h2\" -1 hole(\"p4\")=\"h2\" >= -1\n"
      "(-hole(\"p1\")=\"h3\"+-hole(\"p2\")=\"h3\"+-hole(\"p3\")=\"h3\"+-hole(\"p4\")=\"h3\">=-1) <=> -1 "
      "hole(\"p1\")=\"h3\" -1 hole(\"p2\")=\"h3\" -1 hole(\"p3\")=\"h3\" -1 hole(\"p4\")=\"h3\" >= -1\n"
      "-1 hole(\"p1\")=\"h1\" -1 hole(\"p2\")=\"h1\" -1 hole(\"p3\")=\"h1\" -1 hole(\"p4\")=\"h1\" -7 "
      "[distinct(hole(p) "
      "for p in pigeon)] 2 (-hole(\"p1\")=\"h2\"+-hole(\"p2\")=\"h2\"+-hole(\"p3\")=\"h2\"+-hole(\"p4\")=\"h2\">=-1) 2 "
      "(-hole(\"p1\")=\"h3\"+-hole(\"p2\")=\"h3\"+-hole(\"p3\")=\"h3\"+-hole(\"p4\")=\"h3\">=-1) >= -4\n"
      "1 >= 1 hole(\"p1\")=\"h1\" 1 hole(\"p1\")=\"h2\" 1 hole(\"p1\")=\"h3\" >= 1\n"
      "1 >= 1 hole(\"p2\")=\"h1\" 1 hole(\"p2\")=\"h2\" 1 hole(\"p2\")=\"h3\" >= 1\n"
      "1 >= 1 hole(\"p3\")=\"h1\" 1 hole(\"p3\")=\"h2\" 1 hole(\"p3\")=\"h3\" >= 1\n"
      "1 >= 1 hole(\"p4\")=\"h1\" 1 hole(\"p4\")=\"h2\" 1 hole(\"p4\")=\"h3\" >= 1\n");
  ilp.init(false, false);
  ilp.global.options.verbosity.parse("0");
  [[maybe_unused]] SolveState state = ilp.runFull();
  REQUIRE(state == SolveState::INCONSISTENT);
}

TEST_CASE("If-else") {
  Vocabulary voc;
  Functor p = *voc.createBoolean("p", {});
  Functor q = *voc.createBoolean("q", {});
  Functor r = *voc.createBoolean("r", {});
  Functor c = *voc.createInterpreted("C", {{1}}, 0);
  Functor d = *voc.createInterpreted("D", {{2}}, 0);
  Functor e = *voc.createInterpreted("E", {{3}}, 0);
  Functor f = *voc.createInterpreted("F", {{4}}, 0);
  Functor g = *voc.createFunctor("G", {Type::INT}, {0, 1, 2, 3});
  Term t = O(">=", IE(IE(A(c, {}), A(p, {}), A(d, {})), A(q, {}), IE(A(e, {}), A(r, {}), A(f, {}))), D(2));
  REQUIRE(t->reduceFull()->getRepr() ==
          "(1 if and(p,q), 2 if and(not p,q), 3 if and(not q,r), 4 if and(not q,not r))>=2");
  REQUIRE(t->translateFull()->getRepr() == "(2and(-p,q)+3and(-q,r)+4and(-q,-r)+and(p,q)>=2)");
  p.setInter({}, false);
  Term t2 = O(">=", IE(A(g, {}), A(q, {}), IE(A(c, {}), A(p, {}), A(g, {}))), D(2));
  REQUIRE(t2->reduceFull()->getRepr() == "G>=2");
  Term t3 = O(">=", IE(A(g, {}), O("not", A(p, {})), IE(A(c, {}), A(q, {}), A(g, {}))), D(2));
  REQUIRE(t3->reduceFull()->getRepr() == "G>=2");
}

TEST_CASE("strip top ands") {
  std::vector<DomEl> abc = {DomEl("a"), DomEl("b")};

  Functor p("P", {Type::STRING, Type::STRING});
  Functor q("Q", {Type::STRING});
  q.setDefault(false);
  q.setInter({"a"}, true);
  q.setInter({"b"}, true);

  Term t = all({"x"}, q, O("and", any({"y"}, q, A(p, V("x"), V("y"))), any({"x"}, q, O("not", A(p, V("x"), V("x"))))));

  t = t->instantiateVars(InstVarState::ATTOP);
  CHECK(t->getRepr() ==
        "and(and(any(P(\"a\",y) for y in Q),any(not P(x,x) for x in Q)),and(any(P(\"b\",y) for y in Q),any(not "
        "P(x,x) for x in Q)))");
  std::vector<Term> conjuncts;
  t->stripTopAnds(conjuncts);
  assert(conjuncts.size() == 4);
  IneqTerm it = t->translateFull();
  // Note the coefficient 2 below. It originates from the duplicates introduced by the non-pushed quantor.
  CHECK(it->getRepr() ==
        "(-P(\"a\",\"a\")+-P(\"b\",\"b\")+2or(-P(\"a\",\"a\"),-P(\"b\",\"b\"))+2or(P(\"a\",\"a\"),P(\"a\",\"b\"))+2or("
        "P(\"b\",\"a\"),P(\"b\",\"b\"))>=5)");
  // TODO: saturate / remove doubles in trueIffMax and falseIffMin for IneqTerm
  // E.g., "2or" above
  // TODO: simplify tautologies / inconsistencies for IneqTerm
}

// TODO: push quantors? user's responsability for now
// TODO: smart unnesting
// TODO: skolemization?
// TODO: invariant checks after each phase (e.g., no more variables after grounding)