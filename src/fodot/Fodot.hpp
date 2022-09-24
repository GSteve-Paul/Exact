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

#pragma once

#include <variant>
#include "../auxiliary.hpp"

namespace xct {
class ILP;
}

namespace fodot {

enum class Type { UNKN = 0, INT = 1, BOOL = 2, STRING = 3 };
std::ostream& operator<<(std::ostream& os, const Type& t);
inline bool operator==(enum Type lhs, enum Type rhs) {
  int l = static_cast<int>(lhs);
  int r = static_cast<int>(rhs);
  return l == 0 || r == 0 || l == r;
}
inline bool operator!=(enum Type lhs, enum Type rhs) { return !(lhs == rhs); }
enum class Unknown { UNKNOWN };
std::ostream& operator<<(std::ostream& os, const Unknown& u);

using fo_int = long long;

using DomEl =
    std::variant<fo_int, bool, std::string, Unknown>;  // TODO: store strings in some global vector, use indices
std::ostream& operator<<(std::ostream& os, const DomEl& de);
const std::string toStr(const DomEl& de);
const DomEl _unknown_ = Unknown::UNKNOWN;
const std::string _true_ = "true";
const std::string _false_ = "false";
DomEl toDomEl(const std::string& s);
using Tup = std::vector<DomEl>;
struct tuphash {
  size_t operator()(const Tup& t) const { return xct::aux::hashForList<DomEl>(t); }
};

Type getType(const DomEl& de);
bool hasType(const DomEl& de, Type t);
std::ostream& operator<<(std::ostream& o, const Tup& t);

const std::vector<DomEl> getIntRange(const std::pair<fo_int, fo_int>& extrema);
const std::vector<DomEl> getStringRange(const std::string& prefix, int min, int max);
template <typename T>
const std::pair<fo_int, fo_int> getExtrema(const T& range) {
  assert(!range.empty());
  assert(getType(*range.begin()) == Type::INT);
  fo_int min = std::get<fo_int>(*range.begin());
  fo_int max = min;
  for (const DomEl& de : range) {
    assert(getType(de) == Type::INT);
    fo_int val = std::get<fo_int>(de);
    min = val < min ? val : min;
    max = val > max ? val : max;
  }
  return {min, max};
}

class FirstOrder;
class Functor {
  friend std::ostream& operator<<(std::ostream& o, const Functor& ftor);

 public:
  const std::string name;
  const std::vector<Type> types;  // TODO: remove the output type?
  const std::unordered_set<DomEl> range;

 private:
  DomEl otherwise;  // NOTE: "default" is a reserved keyword ;)
  std::unordered_map<Tup, DomEl, tuphash> interpretation;
  std::unordered_set<Tup, tuphash> domain;
  std::unordered_map<Tup, DomEl, tuphash> extension;
  std::ostream& toStream(std::ostream& o, const std::unordered_map<Tup, DomEl, tuphash>& inter) const;

 public:
  Functor(const std::string& n, const std::vector<Type>& t, const std::vector<DomEl>& r);
  Functor(const std::string& n, const std::vector<Type>& t);  // predicate

  const std::unordered_map<Tup, DomEl, tuphash>& getInter() const;
  DomEl getInter(const Tup& t) const;
  void setInter(const Tup& t, const DomEl& de);
  void setInterUnary(const std::vector<DomEl>&, const DomEl& de);
  void setDefault(const DomEl& de);  // TODO: part of constructor?
  DomEl getDefault() const;
  int getArity() const;
  Type getReturnType() const;
  void addToDomain(const Tup& t);
  void addTo(xct::ILP& ilp);
  void readExtension(xct::ILP& ilp);
  const std::unordered_map<Tup, DomEl, tuphash>& getExtension() const;
  DomEl getExtension(const Tup& t) const;
  const std::vector<Tup> getInterAsRange() const;
  bool isRange() const;
  bool isSet() const;
  const std::vector<DomEl> getInterAsSet() const;
};
std::ostream& operator<<(std::ostream& o, const Functor& ftor);

class NotInRange : public std::exception {
  std::string msg;

 public:
  NotInRange(const Functor& f, const DomEl& de);
  [[nodiscard]] const char* what() const noexcept override;
};
class TypeClash : public std::exception {
  std::string msg;

 public:
  TypeClash(const std::string& m);
  [[nodiscard]] const char* what() const noexcept override;
};
class ArityMismatch : public std::exception {
  std::string msg;

 public:
  ArityMismatch(int expected, int provided, const std::string& message = "");
  [[nodiscard]] const char* what() const noexcept override;
};
void checkArity(int expected, int provided, const std::string& message);
class NoSet : public std::exception {
  std::string msg;

 public:
  NoSet(const Functor& f);
  [[nodiscard]] const char* what() const noexcept override;
};
class Var;
class NotScoped : public std::exception {
  std::string msg;

 public:
  NotScoped(const Var& v);
  [[nodiscard]] const char* what() const noexcept override;
};
class NoRange : public std::exception {
  std::string msg;

 public:
  NoRange(const Functor& f);
  [[nodiscard]] const char* what() const noexcept override;
};

}  // namespace fodot