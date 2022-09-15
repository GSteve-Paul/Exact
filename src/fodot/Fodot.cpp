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

#include "Fodot.hpp"
#include <sstream>
#include "../ILP.hpp"
#include "IneqExpr.hpp"
#include "auxiliary.hpp"
#include "doctest/doctest.h"

namespace fodot {

std::ostream& operator<<(std::ostream& os, const Type& t) {
  if (t == Type::BOOL) return os << "bool";
  if (t == Type::STRING) return os << "string";
  if (t == Type::INT) return os << "int";
  if (t == Type::UNKN) return os << "unknown";
  assert(false);
  return os;
}

std::ostream& operator<<(std::ostream& os, const Unknown& u) { return os << "?"; }

std::ostream& operator<<(std::ostream& os, const DomEl& de) {
  if (std::holds_alternative<std::string>(de)) {
    return os << '\"' << std::get<std::string>(de) << "\"";
  }
  if (std::holds_alternative<fo_int>(de)) {
    return os << std::get<fo_int>(de);
  }
  if (std::holds_alternative<bool>(de)) {
    return os << (std::get<bool>(de) ? "true" : "false");
  }
  if (std::holds_alternative<Unknown>(de)) {
    return os << "unknown";
  }
  assert(false);
  return os;
}

const std::string toStr(const DomEl& de) { return (std::stringstream() << de).str(); }

DomEl toDomEl(const std::string& s) {
  try {
    return std::stol(s);
  } catch (const std::invalid_argument& ia) {
    if (s == _true_) return true;
    if (s == _false_) return false;
    return s;
  }
}

std::vector<DomEl> toDomEls(const std::vector<std::string>& names) {
  return xct::aux::comprehension(names, [](const std::string& name) { return toDomEl(name); });
}

Type getType(const DomEl& de) {
  if (std::holds_alternative<bool>(de)) return Type::BOOL;
  if (std::holds_alternative<fo_int>(de)) return Type::INT;
  if (std::holds_alternative<std::string>(de)) return Type::STRING;
  if (std::holds_alternative<Unknown>(de)) return Type::UNKN;
  assert(false);
  return Type::BOOL;
}
bool hasType(const DomEl& de, Type t) { return de == _unknown_ || getType(de) == t; }

std::ostream& operator<<(std::ostream& o, const Tup& t) {
  o << "(";
  int i = 0;
  for (const auto& de : t) {
    ++i;
    o << de << (i == (int)t.size() ? "" : ",");
  }
  o << ")";
  return o;
}

const std::vector<DomEl> getIntRange(const std::pair<fo_int, fo_int>& extrema) {
  const fo_int& min = extrema.first;
  const fo_int& max = extrema.second;
  assert(max >= min);
  std::vector<DomEl> res;
  res.reserve(max - min + 1);
  for (fo_int i = min; i <= max; ++i) {
    res.push_back(DomEl(i));
  }
  return res;
}

const std::vector<DomEl> getStringRange(const std::string& prefix, int min, int max) {
  assert(max >= min);
  std::vector<DomEl> res;
  res.reserve(max - min + 1);
  for (fo_int i = min; i <= max; ++i) {
    res.push_back(DomEl(prefix + std::to_string(i)));
  }
  return res;
}

NotInRange::NotInRange(const Functor& f, const DomEl& de) : msg() {
  std::stringstream ss;
  ss << "Not possible to interpret " << f.name << " with range " << f.range << " using value " << de << ".";
  msg = ss.str();
}
const char* NotInRange::what() const noexcept { return msg.c_str(); }
TypeClash::TypeClash(const std::string& m) : msg(m) {}
const char* TypeClash::what() const noexcept { return msg.c_str(); }
ArityMismatch::ArityMismatch(int expected, int provided) : msg() {
  std::stringstream ss;
  ss << "Expected arity " << expected << " but got " << provided << ".";
  msg = ss.str();
}
const char* ArityMismatch::what() const noexcept { return msg.c_str(); }
NoSet::NoSet(const Functor& f) : msg() {
  std::stringstream ss;
  ss << f.name << " is not unary or not Boolean or has no finite interpretation, so it cannot be used as set.";
  msg = ss.str();
}
const char* NoSet::what() const noexcept { return msg.c_str(); }
NotScoped::NotScoped(const Var& v) : msg() {
  std::stringstream ss;
  ss << v.name << " does not seem to have been introduced by a scope statement.";
  msg = ss.str();
}
const char* NotScoped::what() const noexcept { return msg.c_str(); }
NoRange::NoRange(const Functor& f) : msg() {
  std::stringstream ss;
  ss << f.name << " is not Boolean or has no finite interpretation, so it cannot be used to scope variables.";
  msg = ss.str();
}
const char* NoRange::what() const noexcept { return msg.c_str(); }

fo_int pairDiff(const std::pair<fo_int, fo_int>& in) { return in.second - in.first; }

Functor::Functor(const std::string& n, const std::vector<Type>& t, const std::vector<DomEl>& r)
    : name(n), types(t), range(r.begin(), r.end()), otherwise(_unknown_), interpretation() {
  assert(!range.empty());
  assert(!types.empty());
  assert(hasType(*range.begin(), types.back()));
  assert(getReturnType() != Type::INT ||
         pairDiff(getExtrema(range)) + 1 == (fo_int)range.size());  // TODO: only ranges for int variables for now
}
Functor::Functor(const std::string& n, const std::vector<Type>& t)
    : Functor(n, aux::concat(t, {Type::BOOL}), {true, false}) {}

int Functor::getArity() const { return types.size() - 1; }

Type Functor::getReturnType() const { return types.back(); }

const std::unordered_map<Tup, DomEl, tuphash>& Functor::getInter() const { return interpretation; }
const std::unordered_map<Tup, DomEl, tuphash>& Functor::getExtension() const { return extension; }

DomEl Functor::getInter(const Tup& t) const {
  assert((int)t.size() == getArity());
  if (auto it = interpretation.find(t); it != interpretation.end()) {
    return it->second;
  } else {
    return otherwise;
  }
}
DomEl Functor::getExtension(const Tup& t) const {
  assert((int)t.size() == getArity());
  if (auto it = extension.find(t); it != extension.end()) {
    return it->second;
  } else {
    return otherwise;
  }
}

void Functor::setInter(const Tup& t, const DomEl& de) {
  if (interpretation.find(t) != interpretation.end())
    throw std::invalid_argument((std::stringstream() << "Tuple " << t << " already has interpretation "
                                                     << *interpretation.find(t) << " for functor " << name << ".")
                                    .str());
  if (de == _unknown_)
    throw std::invalid_argument(
        (std::stringstream() << "Attempting to set interpretation of " << t << " as unknown.").str());
  if ((int)t.size() != getArity()) throw ArityMismatch(getArity(), t.size());
  for (int i = 0; i < (int)t.size(); ++i) {
    if (!hasType(t[i], types[i]))
      throw TypeClash(
          (std::stringstream() << "Expected type " << types[i] << " for argument " << i << " of tuple " << t << ".")
              .str());
  }
  if (!range.count(de)) throw NotInRange(*this, de);
  interpretation[t] = de;
}

void Functor::setInterUnary(const std::vector<DomEl>& t, const DomEl& de) {
  for (const DomEl& d : t) {
    setInter({d}, de);
  }
}

void Functor::setDefault(const DomEl& de) {
  assert(de == _unknown_ || xct::aux::contains(range, de));
  otherwise = de;
}

DomEl Functor::getDefault() const { return otherwise; }

void Functor::addToDomain(const Tup& t) { domain.insert(t); }

void Functor::addTo(xct::ILP& ilp) {
  switch (getReturnType()) {
    case Type::BOOL: {
      for (const Tup& t : domain) {
        xct::IntVar* iv = ilp.addVar(Terminal(*this, t).getRepr(), 0, 1);
        if (const auto& val = interpretation.find(t); val != interpretation.end()) {
          ilp.fix(iv, std::get<bool>(val->second));
        } else if (otherwise != _unknown_) {
          ilp.fix(iv, std::get<bool>(otherwise));
        }
      }
      return;
    }
    case Type::INT: {
      auto [min, max] = getExtrema(range);
      for (const Tup& t : domain) {
        xct::IntVar* iv = ilp.addVar(Terminal(*this, t).getRepr(), min, max);
        if (const auto& val = interpretation.find(t); val != interpretation.end()) {
          ilp.fix(iv, std::get<fo_int>(val->second));
        } else if (otherwise != _unknown_) {
          ilp.fix(iv, std::get<fo_int>(otherwise));
        }
      }
      return;
    }
    case Type::STRING: {
      // create equality variables F("a")="b"
      std::vector<bigint> ones(range.size(), 1);
      for (const Tup& t : domain) {
        std::vector<xct::IntVar*> vars = xct::aux::comprehension(
            range, [&](const DomEl& de) { return ilp.addVar(Terminal(*this, t, de).getRepr(), 0, 1); });
        if (const auto& val = interpretation.find(t); val != interpretation.end()) {
          ilp.fix(ilp.getVarFor(Terminal(*this, t, val->second).getRepr()), 1);
        } else if (otherwise != _unknown_) {
          ilp.fix(ilp.getVarFor(Terminal(*this, t, otherwise).getRepr()), 1);
        }
        ilp.addConstraint(ones, vars, {}, 1, 1);  // function constraint
      }
      return;
    }
    default: {
      assert(false);
      return;
    }
  }
  // TODO: what with missing values in an int-range?
}

void Functor::readExtension(xct::ILP& ilp) {
  extension.clear();
  if (getReturnType() == Type::BOOL) {
    for (const Tup& tup : domain) {
      extension[tup] = ilp.getLastSolutionFor(ilp.getVarFor(Terminal(*this, tup).getRepr())) == 1;
    }
  } else if (getReturnType() == Type::INT) {
    for (const Tup& tup : domain) {
      extension[tup] = static_cast<fo_int>(ilp.getLastSolutionFor(ilp.getVarFor(Terminal(*this, tup).getRepr())));
    }
  } else if (getReturnType() == Type::STRING) {
    for (const Tup& tup : domain) {
      for (const DomEl& de : range) {
        if (ilp.getLastSolutionFor(ilp.getVarFor(Terminal(*this, tup, de).getRepr())) == 1) {
          extension[tup] = de;
        }
      }
      assert(extension.count(tup));  // function constraint satisfied
    }
  } else {
    assert(false);
  }
  // TODO: check extension conforms with interpretation
  // TODO: partial interpretations that disallow values for a String-functor.
}

const std::vector<Tup> Functor::getInterAsRange() const {
  if (!isRange()) throw NoRange(*this);
  std::vector<Tup> res;
  res.reserve(interpretation.size());
  for (const auto& kv : interpretation) {
    if (kv.second == DomEl(true)) res.push_back(kv.first);
  }
  return res;
}

bool Functor::isRange() const { return getReturnType() == Type::BOOL && getDefault() == DomEl(false); }

bool Functor::isSet() const { return isRange() && getArity() == 1; }

const std::vector<DomEl> Functor::getInterAsSet() const {
  if (!isSet()) throw NoSet(*this);
  std::vector<DomEl> res;
  res.reserve(interpretation.size());
  for (const auto& kv : interpretation) {
    if (kv.second == DomEl(false)) continue;
    res.push_back(kv.first[0]);
  }
  return res;
}

std::ostream& Functor::toStream(std::ostream& o, const std::unordered_map<Tup, DomEl, tuphash>& inter) const {
  o << "{";
  if (getReturnType() == Type::BOOL && getDefault() == DomEl{false}) {
    int i = 0;
    for (const auto& pair : inter) {
      ++i;
      if (pair.second == DomEl{true}) {
        o << pair.first << (i == (int)inter.size() ? "" : ", ");
      }
    }
    o << "}.";
  } else {
    int i = 0;
    for (const auto& pair : inter) {
      ++i;
      o << pair.first << "->" << pair.second << (i == (int)inter.size() ? "" : ", ");
    }
    o << "}";
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const Functor& ftor) {
  o << ftor.name;
  if (ftor.interpretation.empty() && ftor.getDefault() == _unknown_) {
    o << ":";
    for (int i = 0; i < int(ftor.types.size()) - 1; ++i) o << " " << ftor.types[i];
    o << " -> {" << ftor.range << "}";
  } else {
    if (!ftor.interpretation.empty()) {
      ftor.toStream(o << " := ", ftor.interpretation);
    }
    if (ftor.getDefault() != _unknown_) {
      o << " else " << ftor.getDefault();
    }
  }
  if (!ftor.extension.empty()) {
    ftor.toStream(o << " extension: ", ftor.extension);
  }

  //  o << "\nrange:";
  //  for (const DomEl& de : ftor.range) o << " " << de;
  //  if (!ftor.domain.empty()) {
  //    o << " domain:";
  //    for (const Tup& t : ftor.domain) o << " " << t;
  //  }
  return o;
}

}  // namespace fodot

using namespace fodot;

TEST_CASE("Bool domain element should be different from Int") { CHECK(DomEl{0} != DomEl{false}); }

TEST_CASE("Function interpretation should throw correct exceptions") {
  Functor p("P", {Type::STRING, Type::BOOL}, {true, false});
  CHECK_THROWS_AS(p.setInter({"green"}, "green"), const NotInRange&);
  CHECK_THROWS_AS(p.setInter({}, false), const ArityMismatch&);
  CHECK_THROWS_AS(p.setInter({false}, false), const TypeClash&);
}
