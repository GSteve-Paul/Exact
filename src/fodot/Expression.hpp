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

/**
 * expression hierarchy:
 *
 * phase 1 (RawExpr):
 *  operator (interpreted functors)
 *   unary: ~ - / (involutive) [pushable]
 *   nary: & | + * (commutative, associative) [mergable]
 *   =
 *   ite
 *   < =< > >=
 *   => <=
 *  application
 *  terminal:
 *   domain element
 *   variable
 *  first order:
 *   simple: ! ? count sum (will be grounded to nary)
 *   complex: alldiff min max even odd (will be transformed)
 *
 *  phase 2 (still nested):
 *   ~ - /
 *   and or +bool +int *
 *   =string
 *   ite_int ite_string
 *   >
 *   app_int app_bool (potentially interpreted functor?)
 *   domel
 *   what with different app argument types?
 *
 *  phase 3 (IneqExpr):
 *   weighted sum
 *   geq
 *   terminal (unsigned)
 */
/**
 * Steps:
 * phase 1:
 * - translate (replace complex FO with simple FO, remove implies, iff, ...)
 * - ground
 * phase 2:
 * - unnest (introduces potential knowns but no quantifiers)
 * - remove knowns
 * - push negations
 * - toIneq (transforms to IneqExpr expressions)
 * phase 3:
 * - flatten weightedsums
 * - mergMin, mergeMax
 * - addTo (add to ILP)
 */
/**
 * order of operators:
 *
 * - [* / %] + (ite?) [> >= = !=] not and or implies iff ite def
 */

#pragma once

#include "Fodot.hpp"

namespace xct {
class ILP;
}

namespace fodot {

enum class Op {
  Not,
  And,
  Or,
  Implies,
  Iff,
  Ite,
  Minus,
  Plus,
  Times,
  Greater,
  StrictGreater,
  Equals,
  Exists,
  Forall,
  Count,
  Sum,
  Alldiff
};
const std::string& getString(Op o);
Type getOutType(Op o);
bool hasInType(Op o, Type t);
std::ostream& operator<<(std::ostream& os, const Op& t);

class RawExpr;
class IneqExpr;
using Term = std::shared_ptr<const RawExpr>;
using IneqTerm = std::shared_ptr<const IneqExpr>;

class Expression {
 public:
  const Type type;
  Expression(Type t);
  virtual ~Expression(){};

  virtual const std::string getRepr() const = 0;  // representation of expression that is used as its variable name.
  // NOTE: repr is used as ILP-variable, so same repr implies equivalent Expression!
};

std::ostream& operator<<(std::ostream& os, const std::shared_ptr<const Expression>& t);
std::ostream& operator<<(std::ostream& os, const std::shared_ptr<const RawExpr>& t);

class Var;
struct varhash {
  size_t operator()(const Var& v) const;
};
enum class InstVarState { ALL, ATTOP, NOTATTOP };
struct Scope {
  const std::vector<std::string> vars;
  const std::vector<Tup> range;
  const std::string rangename;
  void checkInvariants() const;
  Scope(const std::vector<std::string>& vs, const Functor& f);
  Scope(const std::vector<std::string>& vs, const std::vector<Tup>& r, const std::string& rn);
};

class RawExpr : public Expression, public std::enable_shared_from_this<const RawExpr> {
 public:
  RawExpr(Type t) : Expression(t){};
  virtual ~RawExpr(){};

  virtual Term deepCopy() const = 0;  // TODO: not used, remove?
  virtual void checkType() const = 0;
  virtual const std::vector<Term> getChildren() const = 0;       // TODO: not used, remove?
  virtual const std::unordered_set<DomEl> getRange() const = 0;  // will be used for unnesting
  virtual IneqTerm toIneq() const = 0;
  virtual Term translate() const = 0;  // removes implies/iff
  virtual Term pushNegation(bool neg = false) const = 0;
  virtual Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const = 0;
  Term instantiateVars(InstVarState ivs = InstVarState::ALL) const;
  virtual std::pair<Term, DomEl> reduceJustifieds() const = 0;
  virtual void stripTopAnds(std::vector<Term>& out) const;

  Term reduceFull() const;
  IneqTerm translateFull() const;
};

class Val;
class FirstOrder;
class Application;
class Operator;

// TODO: use variadic arguments
std::shared_ptr<Val> D(const DomEl& de);
std::shared_ptr<Var> V(const std::string& s);
std::shared_ptr<Application> A(Functor& f, const std::initializer_list<Term>& args);
std::shared_ptr<Application> A(Functor& f, const Term& arg1);
std::shared_ptr<Application> A(Functor& f, const Term& arg1, const Term& arg2);
std::shared_ptr<Application> A(Functor& f, const Term& arg1, const Term& arg2, const Term& arg3);
std::shared_ptr<Application> A(Functor& f, const Term& arg1, const Term& arg2, const Term& arg3, const Term& arg4);
std::shared_ptr<Operator> O(const std::string& op, const std::initializer_list<Term>& args);
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1);
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1, const Term& arg2);
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1, const Term& arg2, const Term& arg3);
std::shared_ptr<Operator> O(const std::string& op, const Term& arg1, const Term& arg2, const Term& arg3,
                            const Term& arg4);
std::shared_ptr<FirstOrder> all(const std::initializer_list<Scope>& scs, const Term& arg);
std::shared_ptr<FirstOrder> all(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg);
std::shared_ptr<FirstOrder> any(const std::initializer_list<Scope>& scs, const Term& arg);
std::shared_ptr<FirstOrder> any(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg);
std::shared_ptr<FirstOrder> unique(const std::initializer_list<Scope>& scs, const Term& arg);
std::shared_ptr<FirstOrder> unique(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg);
std::shared_ptr<FirstOrder> sum(const std::initializer_list<Scope>& scs, const Term& arg);
std::shared_ptr<FirstOrder> sum(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg);
std::shared_ptr<FirstOrder> count(const std::initializer_list<Scope>& scs, const Term& arg);
std::shared_ptr<FirstOrder> count(const std::initializer_list<std::string>& vs, const Functor& f, const Term& arg);

class Val : public RawExpr {
 public:
  const DomEl de;

  Val(const DomEl& d);
  void checkType() const;
  Term deepCopy() const;
  void collectDomains() const;
  const std::string getRepr() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;
};

class Operator : public RawExpr {
 public:
  const Op symbol;
  Operator(Op o);
  virtual ~Operator(){};
};

class Unary : public Operator {
  const Term argument;

 public:
  Unary(Op o, const Term& arg);
  Term deepCopy() const;
  void checkType() const;
  void collectDomains() const;
  const std::string getRepr() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;
};

class Binary : public Operator {
  const Term arg1;
  const Term arg2;

 public:
  Binary(Op o, const Term& a1, const Term& a2);
  Term deepCopy() const;
  void checkType() const;
  void collectDomains() const;
  const std::string getRepr() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;
};

class Nary : public Operator {
  const std::vector<Term> arguments;

 public:
  Nary(Op o, const std::vector<Term>& args);
  Term deepCopy() const;
  void checkType() const;
  void collectDomains() const;
  const std::string getRepr() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;
  void stripTopAnds(std::vector<Term>& out) const;
};

class Application : public RawExpr {
  friend class Binary;
  Functor& functor;
  const std::vector<Term> arguments;

 public:
  Application(Functor& f, const std::vector<Term>& args);
  Term deepCopy() const;
  void checkType() const;
  void collectDomains() const;
  const std::string getRepr() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;
};

class Var : public RawExpr {
 public:
  const std::string name;

  Var(const std::string n);
  const std::string getRepr() const;
  Term deepCopy() const;
  void checkType() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;

  bool operator==(const Var& other) const;
};
std::ostream& operator<<(std::ostream& os, const Var& v);

class FirstOrder : public Operator {
 public:
  const std::vector<Scope> scopes;
  const Term argument;
  FirstOrder(Op o, const std::vector<Scope>& scs, const Term& arg);

  const std::string getRepr() const;
  Term deepCopy() const;
  void checkType() const;
  const std::vector<Term> getChildren() const;
  const std::unordered_set<DomEl> getRange() const;
  IneqTerm toIneq() const;
  Term translate() const;
  Term pushNegation(bool neg = false) const;
  Term instantiateVars(const std::unordered_map<Var, DomEl, varhash>& var2de, InstVarState ivs) const;
  std::pair<Term, DomEl> reduceJustifieds() const;
};

// TODO
// class Ite : public Expression {};
// d = b if a else c
// clausifies to:
// ~a | d | ~b
// ~a | b | ~d
// a | d | ~c
// a | c | ~d

// Push ite?
// P(F(C() if Q() else "a")
// ?x: (?y: F(x)=y & P(y)) & (Q() => x=C()) & (~Q() => x="a").

// P(F(C()) if Q() else F("a"))
// ?x: P(x) & (Q() => x=F(C())) & (~Q() => x=F("a"))
// ?x: P(x) & [Q() => (?y: y=C() & x=F(y))] & [~Q() => x=F("a")]
// (!x: C()=x => P(x)) if Q() else P("a")
//

}  // namespace fodot
