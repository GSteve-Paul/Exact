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

#include "Expression.hpp"

namespace fodot {

enum class PushMinusState { OK, STILLMINUS, FIXOFFSET };

class Geq;
class IneqExpr : public Expression, public std::enable_shared_from_this<IneqExpr> {
 public:
  IneqExpr() : Expression(Type::INT){};
  ~IneqExpr(){};

  virtual void collectDomains() const = 0;
  virtual void addTo(xct::ILP& ilp) const = 0;
  virtual void addToAsTop(xct::ILP& ilp) const = 0;

  virtual IneqTerm flatten() const = 0;
  virtual std::pair<IneqTerm, bool> mergeMin() const = 0;
  virtual std::pair<IneqTerm, bool> mergeMax() const = 0;
  virtual std::pair<IneqTerm, PushMinusState> pushMinus(bool minus) const = 0;
  virtual IneqTerm bigM() const = 0;

  virtual fo_int getMin() const = 0;
  virtual fo_int getMax() const = 0;

  IneqTerm reduceFull() const;
};
std::ostream& operator<<(std::ostream& os, const IneqTerm& t);

class Geq;
class WeightedSum : public IneqExpr {
  friend class Geq;
  std::unordered_map<IneqTerm, fo_int> terms;  // mapping to coefficients
  fo_int offset = 0;

  void cleanZeroes();
  std::shared_ptr<WeightedSum> pushMinus_(bool minus, bool addOne) const;
  std::shared_ptr<WeightedSum> flatten_() const;

 public:
  WeightedSum(const std::vector<fo_int>& coefs, const std::vector<IneqTerm>& vars, const fo_int& os);
  void collectDomains() const;
  IneqTerm flatten() const;
  std::pair<IneqTerm, bool> mergeMin() const;
  std::pair<IneqTerm, bool> mergeMax() const;
  std::pair<IneqTerm, PushMinusState> pushMinus(bool minus) const;
  IneqTerm bigM() const;

  void addTo(xct::ILP& ilp) const;
  void addToAsTop(xct::ILP& ilp) const;
  const std::string getRepr() const;
  const std::string getReprLHS(char connective) const;

  void add(const fo_int& coef, const IneqTerm& it);
  void merge(const WeightedSum& other, const fo_int& factor);
  fo_int getMin() const;
  fo_int getMax() const;
};

class Geq : public IneqExpr {
  // >= 0 expression
  const std::shared_ptr<const WeightedSum> argument;

 public:
  Geq(const std::shared_ptr<const WeightedSum>& arg);
  void collectDomains() const;
  IneqTerm flatten() const;
  std::pair<IneqTerm, bool> mergeMin() const;
  std::pair<IneqTerm, bool> mergeMax() const;
  std::pair<IneqTerm, PushMinusState> pushMinus(bool minus) const;
  IneqTerm bigM() const;

  void addTo(xct::ILP& ilp) const;
  void addToAsTop(xct::ILP& ilp) const;
  const std::string getRepr() const;
  fo_int getMin() const;
  fo_int getMax() const;
  bool trueIffMax() const;
  bool falseIffMin() const;
};

class Terminal : public IneqExpr {
  Functor& functor;
  const Tup arguments;  // NOTE: contains output argument in case of Type::STRING return type

 public:
  Terminal(Functor& f, const std::vector<DomEl>& args);
  Terminal(Functor& f, const std::vector<DomEl>& args, const DomEl& extra);
  void collectDomains() const;
  IneqTerm flatten() const;
  std::pair<IneqTerm, bool> mergeMin() const;
  std::pair<IneqTerm, bool> mergeMax() const;
  std::pair<IneqTerm, PushMinusState> pushMinus(bool minus) const;
  IneqTerm bigM() const;

  void addTo(xct::ILP& ilp) const;
  void addToAsTop(xct::ILP& ilp) const;
  const std::string getRepr() const;
  fo_int getMin() const;
  fo_int getMax() const;
};

}  // namespace fodot
