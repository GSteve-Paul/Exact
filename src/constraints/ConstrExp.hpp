/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2023 Jo Devriendt, Nonfiction Software

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

#pragma once

#include <memory>
#include <sstream>
#include "../Global.hpp"
#include "../datastructures/SolverStructs.hpp"
#include "../typedefs.hpp"
#include "ConstrExpPools.hpp"
#include "ConstrSimple.hpp"

namespace xct {

enum class AssertionStatus { NONASSERTING, ASSERTING, FALSIFIED };

struct ConstraintAllocator;
class Solver;
class Heuristic;
class Equalities;
class Implications;
struct IntSet;

struct ConstrExpSuper {
  // protected:
  // for some reason (templates?) copyTo_ cannot acces external vars and indexes if protected
  std::vector<Var> vars;   // variables in the constraint
  std::vector<int> index;  // maps variables to their index in vars, -1 implies the variable has coefficient 0

 public:
  Global& global;
  Origin orig;
  std::stringstream proofBuffer;

  void resetBuffer(ID proofID);
  void resetBuffer(const std::string& line);

  int nVars() const { return vars.size(); }
  int nNonZeroVars() const;
  const std::vector<Var>& getVars() const { return vars; }
  bool used(Var v) const { return index[v] >= 0; }
  void reverseOrder();

  void weakenLast();
  void popLast();

  bool hasNoUnits(const IntMap<int>& level) const;
  bool isUnitConstraint() const;
  // NOTE: only equivalence preserving operations over the Bools!
  void postProcess(const IntMap<int>& level, const std::vector<int>& pos, const Heuristic& heur, bool sortFirst,
                   Stats& stats);
  void strongPostProcess(Solver& solver);

  ConstrExpSuper(Global& g);
  virtual ~ConstrExpSuper() = default;

  virtual void copyTo(const Ce32& ce) const = 0;
  virtual void copyTo(const Ce64& ce) const = 0;
  virtual void copyTo(const Ce96& ce) const = 0;
  virtual void copyTo(const Ce128& ce) const = 0;
  virtual void copyTo(const CeArb& ce) const = 0;

  virtual CeSuper clone(ConstrExpPools& ce) const = 0;
  virtual CRef toConstr(ConstraintAllocator& ca, bool locked, ID id) const = 0;
  virtual std::unique_ptr<ConstrSimpleSuper> toSimple() const = 0;

  virtual void resize(size_t s) = 0;
  virtual bool isReset() const = 0;
  virtual void reset(bool partial) = 0;

  virtual double getStrength() const = 0;

  virtual Lit getLit(Var) const = 0;
  virtual bool hasLit(Lit l) const = 0;
  virtual bool hasVar(Var v) const = 0;
  virtual bool saturatedLit(Lit l) const = 0;
  virtual bool saturatedVar(Var v) const = 0;

  virtual void weaken(Var v) = 0;
  virtual void weaken(const aux::predicate<Lit>& toWeaken) = 0;

  virtual bool hasNegativeSlack(const IntMap<int>& level) const = 0;
  virtual bool isTautology() const = 0;
  virtual bool isInconsistency() const = 0;
  virtual bool isSatisfied(const std::vector<Lit>& assignment) const = 0;
  virtual unsigned int getLBD(const IntMap<int>& level) const = 0;

  virtual void removeUnitsAndZeroes(const IntMap<int>& level, const std::vector<int>& pos) = 0;
  virtual void removeZeroes() = 0;
  virtual bool hasNoZeroes() const = 0;
  virtual void removeEqualities(Equalities& equalities, bool saturate) = 0;
  virtual void selfSubsumeImplications(const Implications& implications) = 0;

  virtual void saturate(const std::vector<Var>& vs, bool check, bool sorted) = 0;
  virtual void saturate(bool check, bool sorted) = 0;
  virtual bool isSaturated() const = 0;
  virtual bool isSaturated(const aux::predicate<Lit>& toWeaken) const = 0;
  virtual void getSaturatedLits(IntSet& out) const = 0;
  virtual void saturateAndFixOverflow(const IntMap<int>& level, int bitOverflow, int bitReduce, Lit asserting) = 0;
  virtual void saturateAndFixOverflowRational() = 0;
  virtual bool fitsInDouble() const = 0;
  virtual bool largestCoefFitsIn(int bits) const = 0;

  virtual bool divideByGCD() = 0;
  virtual bool divideTo(double limit, const aux::predicate<Lit>& toWeaken) = 0;
  virtual AssertionStatus isAssertingBefore(const IntMap<int>& level, int lvl) const = 0;
  virtual std::pair<int, bool> getAssertionStatus(const IntMap<int>& level, const std::vector<int>& pos,
                                                  std::vector<Lit>& litsByPos) const = 0;
  virtual void heuristicWeakening(const IntMap<int>& level, const std::vector<int>& pos) = 0;

  virtual bool simplifyToCardinality(bool equivalencePreserving, int cardDegree) = 0;
  virtual bool isCardinality() const = 0;
  virtual int getCardinalityDegree() const = 0;
  virtual int getMaxStrengthCardinalityDegree(std::vector<int>& cardPoints) const = 0;
  virtual void getCardinalityPoints(std::vector<int>& cardPoints) const = 0;
  virtual int getCardinalityDegreeWithZeroes() = 0;
  virtual void simplifyToClause() = 0;
  virtual bool isClause() const = 0;
  virtual void simplifyToUnit(const IntMap<int>& level, const std::vector<int>& pos, Var v_unit) = 0;

  virtual bool isSortedInDecreasingCoefOrder() const = 0;
  virtual void sortInDecreasingCoefOrder(const std::function<bool(Var, Var)>& tiebreaker) = 0;
  virtual void sortWithCoefTiebreaker(const std::function<int(Var, Var)>& comp) = 0;

  virtual void toStreamAsOPBlhs(std::ostream& o, bool withConstant) const = 0;
  virtual void toStreamAsOPB(std::ostream& o) const = 0;
  virtual void toStreamWithAssignment(std::ostream& o, const IntMap<int>& level, const std::vector<int>& pos) const = 0;
  virtual void toStreamPure(std::ostream& o) const = 0;

  virtual int resolveWith(const Lit* data, unsigned int size, unsigned int deg, ID id, Lit l, const IntMap<int>& level,
                          const std::vector<int>& pos, IntSet& actSet) = 0;
  virtual int resolveWith(const Term32* terms, unsigned int size, const long long& degr, ID id, Origin o, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) = 0;
  virtual int resolveWith(const Term64* terms, unsigned int size, const int128& degr, ID id, Origin o, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) = 0;
  virtual int resolveWith(const Term128* terms, unsigned int size, const int128& degr, ID id, Origin o, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) = 0;
  virtual int resolveWith(const Term128* terms, unsigned int size, const int256& degr, ID id, Origin o, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) = 0;
  virtual int resolveWith(const TermArb* terms, unsigned int size, const bigint& degr, ID id, Origin o, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) = 0;
  virtual int subsumeWith(const Lit* data, unsigned int size, unsigned int deg, ID id, Lit l, const IntMap<int>& level,
                          const std::vector<int>& pos, IntSet& saturatedLits) = 0;
  virtual int subsumeWith(const Term32* terms, unsigned int size, const long long& degr, ID id, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) = 0;
  virtual int subsumeWith(const Term64* terms, unsigned int size, const int128& degr, ID id, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) = 0;
  virtual int subsumeWith(const Term128* terms, unsigned int size, const int128& degr, ID id, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) = 0;
  virtual int subsumeWith(const Term128* terms, unsigned int size, const int256& degr, ID id, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) = 0;
  virtual int subsumeWith(const TermArb* terms, unsigned int size, const bigint& degr, ID id, Lit l,
                          const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) = 0;
};
std::ostream& operator<<(std::ostream& o, const ConstrExpSuper& ce);
std::ostream& operator<<(std::ostream& o, const CeSuper& ce);

template <typename SMALL, typename LARGE>  // LARGE should be able to fit the sum of 2^32 SMALLs
struct ConstrExp final : public ConstrExpSuper {
 public:
  LARGE degree = 0;
  LARGE rhs = 0;
  std::vector<SMALL> coefs;  // maps variables to coefficients

 private:
  void add(Var v, SMALL c, bool removeZeroes = false);
  void remove(Var v);  // NOTE: modifies order of variables
  bool increasesSlack(const IntMap<int>& level, Var v) const;
  LARGE calcDegree() const;
  LARGE calcRhs() const;
  bool testConstraint() const;
  bool falsified(const IntMap<int>& level, Var v) const;

 public:
  explicit ConstrExp(Global& g);

  void copyTo(const Ce32& ce) const;
  void copyTo(const Ce64& ce) const;
  void copyTo(const Ce96& ce) const;
  void copyTo(const Ce128& ce) const;
  void copyTo(const CeArb& ce) const;

  CeSuper clone(ConstrExpPools& ce) const;
  CRef toConstr(ConstraintAllocator& ca, bool locked, ID id) const;
  std::unique_ptr<ConstrSimpleSuper> toSimple() const;

  void resize(size_t s);
  bool isReset() const;
  void reset(bool partial);

  double getStrength() const;
  LARGE getRhs() const;
  LARGE getDegree() const;
  SMALL getCoef(Lit l) const;
  SMALL absCoef(Var v) const;
  SMALL nthCoef(int i) const;
  SMALL getLargestCoef(const std::vector<Var>& vs) const;
  SMALL getLargestCoef() const;
  SMALL getSmallestCoef() const;
  LARGE getCutoffVal() const;
  Lit getLit(Var v) const;
  bool hasLit(Lit l) const;
  bool hasVar(Var v) const;
  bool saturatedLit(Lit l) const;
  bool saturatedVar(Var v) const;

  void addRhs(const LARGE& r);
  void addLhs(const SMALL& cf, Lit l);  // TODO: Term?
  void weaken(const SMALL& m, Var v);
  void weaken(Var v);
  void weaken(const aux::predicate<Lit>& toWeaken);

  LARGE getSlack(const IntMap<int>& level) const;
  bool hasNegativeSlack(const IntMap<int>& level) const;
  bool isTautology() const;
  bool isInconsistency() const;
  bool isSatisfied(const std::vector<Lit>& assignment) const;
  unsigned int getLBD(const IntMap<int>& level) const;

  // @post: preserves order of vars
  void removeUnitsAndZeroes(const IntMap<int>& level, const std::vector<int>& pos);
  // @post: mutates order of vars
  void removeZeroes();
  bool hasNoZeroes() const;
  // @post: preserves order of vars and saturates, but may change coefficients, so sorting property is removed
  void removeEqualities(Equalities& equalities, bool saturate);
  // @post: preserves order of vars and saturates
  void selfSubsumeImplications(const Implications& implications);

  // @post: preserves order of vars
  void saturate(const std::vector<Var>& vs, bool check, bool sorted);
  void saturate(Var v);
  void saturate(bool check, bool sorted);
  bool isSaturated() const;
  bool isSaturated(const aux::predicate<Lit>& toWeaken) const;
  void getSaturatedLits(IntSet& out) const;
  /*
   * Fixes overflow
   * @pre @post: hasNoZeroes()
   * @pre @post: isSaturated()
   * @post: nothing else if bitOverflow == 0
   * @post: the largest coefficient is less than 2^bitOverflow
   * @post: the degree and rhs are less than 2^bitOverflow * INF
   * @post: if overflow happened, all division until 2^bitReduce happened
   * @post: the constraint remains conflicting or propagating on asserting
   */
  void fixOverflow(const IntMap<int>& level, int bitOverflow, int bitReduce, const SMALL& largestCoef, Lit asserting);
  void saturateAndFixOverflow(const IntMap<int>& level, int bitOverflow, int bitReduce, Lit asserting);
  /*
   * Fixes overflow for rationals
   * @post: saturated
   * @post: none of the coefficients, degree, or rhs exceed INFLPINT
   */
  void saturateAndFixOverflowRational();
  bool fitsInDouble() const;
  bool largestCoefFitsIn(int bits) const;

  template <typename S, typename L>
  void addUp(const CePtr<S, L>& c, const SMALL& cmult = 1) {
    global.stats.NADDEDLITERALS += c->nVars();
    assert(cmult >= 1);
    if (global.logger.isActive()) Logger::proofMult(proofBuffer << c->proofBuffer.rdbuf(), cmult) << "+ ";
    rhs += static_cast<LARGE>(cmult) * static_cast<LARGE>(c->rhs);
    degree += static_cast<LARGE>(cmult) * static_cast<LARGE>(c->degree);
    for (Var v : c->vars) {
      assert(v < (Var)coefs.size());
      assert(v > 0);
      SMALL val = cmult * static_cast<SMALL>(c->coefs[v]);
      add(v, val, true);
    }
  }

  void invert();
  void multiply(const SMALL& m);
  void divideRoundUp(const LARGE& d);
  void divideRoundDown(const LARGE& d);
  void weakenDivideRound(const LARGE& div, const aux::predicate<Lit>& toWeaken);
  void weakenDivideRoundOrdered(const LARGE& div, const IntMap<int>& level);
  void weakenDivideRoundOrderedCanceling(const LARGE& div, const IntMap<int>& level, const std::vector<int>& pos,
                                         const SMALL& mult, const ConstrExp<SMALL, LARGE>& confl);
  void weakenMIROrdered(const LARGE& d, const IntMap<int>& level, const SMALL& to, const SMALL& reasonCoef);
  void weakenNonDivisible(const aux::predicate<Lit>& toWeaken, const LARGE& div);
  void weakenNonDivisible(const LARGE& div, const IntMap<int>& level);
  void weakenNonDivisibleCanceling(const LARGE& div, const IntMap<int>& level, const SMALL& mult,
                                   const ConstrExp<SMALL, LARGE>& confl);
  void repairOrder();
  void weakenSuperfluous(const LARGE& div, bool sorted, const aux::predicate<Var>& toWeaken);
  void weakenSuperfluous(const LARGE& div);
  void weakenSuperfluousCanceling(const LARGE& div, const std::vector<int>& pos);
  SMALL weakenSuperfluousMIR(const LARGE& div, SMALL& amount);
  bool weakenUseless(const LARGE& div, SMALL& amount);
  void dropDegree(const LARGE& d, SMALL& amount);
  void applyMIR(const LARGE& d, const std::function<Lit(Var)>& toLit);
  void applyMIRalt(const LARGE& d);
  void compare(const CePtr<SMALL, LARGE>& other) const;


  bool divideByGCD();
  bool divideTo(double limit, const aux::predicate<Lit>& toWeaken);
  const SMALL findWeakenAmount(const LARGE& d, const SMALL& to);
  AssertionStatus isAssertingBefore(const IntMap<int>& level, int lvl) const;
  // @return: latest decision level that does not make the constraint inconsistent
  // @return: whether or not the constraint is asserting at that level
  std::pair<int, bool> getAssertionStatus(const IntMap<int>& level, const std::vector<int>& pos,
                                          std::vector<Lit>& litsByPos) const;
  // @post: preserves order after removeZeroes()
  void weakenNonImplied(const IntMap<int>& level, const LARGE& slack);
  // @post: preserves order after removeZeroes()
  bool weakenNonImplying(const IntMap<int>& level, const SMALL& propCoef, const LARGE& slack);
  // @post: preserves order after removeZeroes()
  void heuristicWeakening(const IntMap<int>& level, const std::vector<int>& pos);

  // @post: preserves order
  template <typename T>
  void weakenSmalls(const T& limit) {
    for (Var v : vars) {
      if (aux::abs(coefs[v]) < limit) {
        weaken(v);
      }
    }
    saturate(true, false);
  }

  LARGE absCoeffSum() const;

  // @post: preserves order of vars
  bool simplifyToCardinality(bool equivalencePreserving, int cardDegree);
  bool isCardinality() const;
  int getCardinalityDegree() const;
  int getMaxStrengthCardinalityDegree(std::vector<int>& cardPoints) const;
  void getCardinalityPoints(std::vector<int>& cardPoints) const;
  int getCardinalityDegreeWithZeroes();
  void simplifyToClause();
  bool isClause() const;
  void simplifyToUnit(const IntMap<int>& level, const std::vector<int>& pos, Var v_unit);

  bool isSortedInDecreasingCoefOrder() const;
  void sortInDecreasingCoefOrder(const std::function<bool(Var, Var)>& tiebreaker);
  void sortWithCoefTiebreaker(const std::function<int(Var, Var)>& comp);

  void toStreamAsOPBlhs(std::ostream& o, bool withConstant) const;
  void toStreamAsOPB(std::ostream& o) const;
  void toStreamWithAssignment(std::ostream& o, const IntMap<int>& level, const std::vector<int>& pos) const;
  void toStreamPure(std::ostream& o) const;

  int resolveWith(const Lit* data, unsigned int size, unsigned int deg, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& actSet);
  int resolveWith(const Term32* terms, unsigned int size, const long long& degr, ID id, Origin o, Lit l,
                  const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet);
  int resolveWith(const Term64* terms, unsigned int size, const int128& degr, ID id, Origin o, Lit l,
                  const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet);
  int resolveWith(const Term128* terms, unsigned int size, const int128& degr, ID id, Origin o, Lit l,
                  const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet);
  int resolveWith(const Term128* terms, unsigned int size, const int256& degr, ID id, Origin o, Lit l,
                  const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet);
  int resolveWith(const TermArb* terms, unsigned int size, const bigint& degr, ID id, Origin o, Lit l,
                  const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet);
  int subsumeWith(const Lit* data, unsigned int size, unsigned int deg, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& saturatedLits);
  int subsumeWith(const Term32* terms, unsigned int size, const long long& degr, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& saturatedLits);
  int subsumeWith(const Term64* terms, unsigned int size, const int128& degr, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& saturatedLits);
  int subsumeWith(const Term128* terms, unsigned int size, const int128& degr, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& saturatedLits);
  int subsumeWith(const Term128* terms, unsigned int size, const int256& degr, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& saturatedLits);
  int subsumeWith(const TermArb* terms, unsigned int size, const bigint& degr, ID id, Lit l, const IntMap<int>& level,
                  const std::vector<int>& pos, IntSet& saturatedLits);

 private:
  template <typename CF, typename DG>
  void initFixOverflow(const Term<CF>* terms, unsigned int size, const DG& degr, ID id, Origin o,
                       const IntMap<int>& level, const std::vector<int>& pos, Lit asserting) {
    orig = o;
    assert(size > 0);
    DG div = 1;
    int bitOverflow = global.options.bitsOverflow.get();
    int bitReduce = global.options.bitsReduced.get();
    if (bitOverflow > 0) {
      DG _rhs = degr;
      for (unsigned int i = 0; i < size; ++i) {
        _rhs -= terms[i].l < 0 ? aux::abs(terms[i].c) : 0;
      }
      DG maxVal =
          std::max<DG>(aux::abs(terms[0].c), std::max<DG>(degr, aux::abs(_rhs)) / INF);  // largest coef in front
      if (maxVal > 0 && (int)aux::msb(maxVal) >= bitOverflow) {
        div = aux::ceildiv<DG>(maxVal, aux::powtwo<DG>(bitReduce) - 1);
      }
    }
    if (div == 1) {
      for (unsigned int i = 0; i < size; ++i) {
        assert(bitOverflow == 0 || (int)aux::msb(aux::ceildiv<DG>(aux::abs(terms[i].c), div)) < bitOverflow);
        addLhs(static_cast<SMALL>(aux::abs(terms[i].c)), terms[i].l);
      }
      addRhs(static_cast<LARGE>(degr));
    } else {
      assert(div > 1);
      DG weakenedDegree = degr;
      for (unsigned int i = 0; i < size; ++i) {
        Lit l = terms[i].l;
        CF cf = aux::abs(terms[i].c);
        if (!isFalse(level, l) && l != asserting) {
          addLhs(static_cast<SMALL>(cf / div), l);  // partial weakening
          weakenedDegree -= cf % div;
        } else {
          assert((int)aux::msb(aux::ceildiv<DG>(cf, div)) < bitOverflow);
          addLhs(static_cast<SMALL>(aux::ceildiv<DG>(cf, div)), l);
        }
      }
      addRhs(static_cast<LARGE>(aux::ceildiv<DG>(weakenedDegree, div)));
    }
    if (global.logger.isActive()) {
      resetBuffer(id);
      if (div > 1) {
        for (unsigned int i = 0; i < size; ++i) {
          Lit l = terms[i].l;
          if (!isFalse(level, l) && l != asserting && aux::abs(terms[i].c) % div != 0) {
            Logger::proofWeaken(proofBuffer, l, -(aux::abs(terms[i].c) % div));
          }
        }
        Logger::proofDiv(proofBuffer, div);
      }
    }
    repairOrder();
    removeUnitsAndZeroes(level, pos);
    saturate(true, true);
  }

  template <typename CF, typename DG>
  int genericResolve(const Term<CF>* terms, unsigned int size, const DG& degr, ID id, Origin o, Lit asserting,
                     const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
    // "this" is the conflict constraint.
    // The terms, degree, and other information from the reason constraint are in the arguments.
    assert(getCoef(-asserting) > 0);
    assert(hasNoZeroes());

    // take an empty reason CE
    CePtr<SMALL, LARGE> reason = global.cePools.take<SMALL, LARGE>();
    // add its data
    reason->initFixOverflow(terms, size, degr, id, o, level, pos, asserting);
    // asserting literal has positive coefficient in reason
    assert(reason->getCoef(asserting) > 0);
    assert(reason->getCoef(asserting) > reason->getSlack(level));

    // negation of asserting literal has positive coefficient in conflict
    const SMALL conflCoef = getCoef(-asserting);
    assert(conflCoef > 0);
    if (reason->getCoef(asserting) == 1) {  // just multiply, nothing else matters as slack is =< 0
      reason->multiply(conflCoef);
      assert(reason->getSlack(level) <= 0);
    } else {
      if (global.options.multBeforeDiv) {
        reason->multiply(conflCoef);
      }
      const SMALL reasonCoef = reason->getCoef(asserting);
      assert(reasonCoef > 0);
      if (global.options.division.is("rto")) {
        reason->weakenMIROrdered(reasonCoef, level, conflCoef, reasonCoef);
        multiply(reason->getCoef(asserting));
        reason->multiply(conflCoef);
        assert(reason->getSlack(level) <= 0);
      } else {
        const LARGE reasonSlack = reason->getSlack(level);
        if (global.options.division.is("slack+1") && reasonSlack > 0 && reasonCoef / (reasonSlack + 1) < conflCoef) {
          reason->weakenMIROrdered(reasonSlack + 1, level, conflCoef, reasonCoef);
          reason->multiply(aux::ceildiv(conflCoef, reason->getCoef(asserting)));
          assert(reason->getSlack(level) <= 0);
        } else {
          assert(global.options.division.is("mindiv") || reasonSlack <= 0 ||
                 reasonCoef / (reasonSlack + 1) >= conflCoef);
          assert(!global.options.multBeforeDiv || conflCoef == aux::gcd(conflCoef, reasonCoef));
          SMALL gcd = global.options.multBeforeDiv ? conflCoef : aux::gcd(conflCoef, reasonCoef);
          const SMALL minDiv = reasonCoef / gcd;
          SMALL bestDiv = minDiv;
          if (bestDiv <= reasonSlack) {
            // quick heuristic search for small divisor larger than slack
            bestDiv = reasonCoef;
            SMALL tmp;
            SMALL pp;
            for (int p : {5, 3, 2}) {
              pp = 1;
              while ((gcd % p) == 0) {
                gcd /= p;
                tmp = reasonCoef / gcd;
                if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
                tmp = minDiv * gcd;
                if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
                pp *= p;
                tmp = reasonCoef / pp;
                if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
                tmp = minDiv * pp;
                if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
              }
            }
          }

          assert(bestDiv > reasonSlack);
          assert(reasonCoef % bestDiv == 0);
          assert(conflCoef % (reasonCoef / bestDiv) == 0);
          const SMALL mult = conflCoef / (reasonCoef / bestDiv);
          if (global.options.caCancelingUnkns) {
            for (Var v : reason->vars) {
              Lit l = reason->getLit(v);
              global.stats.NUNKNOWNROUNDEDUP += isUnknown(pos, v) && getCoef(-l) >= mult;
            }
            reason->weakenDivideRoundOrderedCanceling(bestDiv, level, pos, mult, *this);
            reason->multiply(mult);
            // NOTE: since canceling unknowns are rounded up, the reason may have positive slack
          } else {
            reason->weakenMIROrdered(bestDiv, level, mult, reasonCoef);
            const SMALL newMult = conflCoef / reason->getCoef(asserting);
            reason->multiply(newMult);
            assert(reason->getSlack(level) <= 0);
          }
        }
      }
    }

    assert(reason->getCoef(asserting) >= conflCoef);
    assert(reason->getCoef(asserting) < 2 * conflCoef);
    assert(global.options.division.is("slack+1") || conflCoef == reason->getCoef(asserting));

    // In most cases, at this point, the reason coefficient is equal to the conflict coefficient
    // and the reason slack is at most zero, so we can safely add the reason to the conflict.

    for (Var v : reason->vars) {
      Lit ll = reason->getLit(v);
      if (isFalse(level, ll)) {
        actSet.add(v);
      }
    }

    LARGE oldDegree = getDegree();
    // add reason to conflict
    addUp(reason);

    std::vector<Var>& varsToCheck = oldDegree <= getDegree() ? reason->vars : vars;
    SMALL largestCF = getLargestCoef(varsToCheck);
    if (largestCF > getDegree()) {
      saturate(varsToCheck, false, false);
      largestCF = static_cast<SMALL>(getDegree());
    }
    fixOverflow(level, global.options.bitsOverflow.get(), global.options.bitsReduced.get(), largestCF, 0);
    assert(getCoef(-asserting) <= 0);
    assert(hasNegativeSlack(level));

    return reason->getLBD(level);
  }

  //@post: variable vector vars is not changed, but coefs[toVar(toSubsume)] may become 0
  template <typename CF, typename DG>
  int genericSubsume(const Term<CF>* terms, unsigned int size, const DG& degr, ID id, Lit toSubsume,
                     const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
    assert(getCoef(-toSubsume) > 0);
    assert(isSaturated());

    DG weakenedDeg = degr;
    assert(weakenedDeg > 0);
    for (unsigned int i = 0; i < size; ++i) {
      Lit l = terms[i].l;
      if (l != toSubsume && !saturatedLits.has(l) && !isUnit(level, -l)) {
        weakenedDeg -= aux::abs(terms[i].c);
        if (weakenedDeg <= 0) {
          return 0;
        }
      }
    }
    assert(weakenedDeg > 0);
    SMALL& cf = coefs[toVar(toSubsume)];
    const SMALL mult = aux::abs(cf);
    if (cf < 0) {
      rhs -= cf;
    }
    cf = 0;
    saturatedLits.remove(-toSubsume);
    ++global.stats.NSUBSUMESTEPS;

    if (global.logger.isActive()) {
      proofBuffer << id << " ";
      for (unsigned int i = 0; i < size; ++i) {
        Lit l = terms[i].l;
        if (isUnit(level, -l)) {
          assert(l != toSubsume);
          Logger::proofWeakenFalseUnit(proofBuffer, global.logger.getUnitID(pos[toVar(l)]), -aux::abs(terms[i].c));
        } else if (l != toSubsume && !saturatedLits.has(l) && !isUnit(level, -l)) {
          Logger::proofWeaken(proofBuffer, l, -aux::abs(terms[i].c));
        }
      }
      // saturate, divide, multiply, add, saturate
      Logger::proofMult(Logger::proofDiv(proofBuffer << "s ", weakenedDeg), mult) << "+ s ";
    }

    IntSet& lbdSet = global.isPool.take();
    for (unsigned int i = 0; i < size; ++i) {
      Lit l = terms[i].l;
      if (l == toSubsume || saturatedLits.has(l)) {
        lbdSet.add(level[-l] % INF);
      }
    }
    lbdSet.remove(0);  // unit literals and non-falsifieds should not be counted
    int lbd = lbdSet.size();
    assert(lbd > 0);
    global.isPool.release(lbdSet);
    return lbd;
  }

  template <typename S, typename L>
  void copyTo_(const CePtr<S, L>& out) const {
    // TODO: assert whether S/L can fit SMALL/LARGE? Not always possible.
    assert(out->isReset());
    out->degree = static_cast<L>(degree);
    out->rhs = static_cast<L>(rhs);
    out->orig = orig;
    out->vars = vars;
    assert(out->coefs.size() == coefs.size());
    for (Var v : vars) {
      out->coefs[v] = static_cast<S>(coefs[v]);
      assert(used(v));
      assert(!out->used(v));
      out->index[v] = index[v];
    }
    if (global.logger.isActive()) {
      out->proofBuffer.str(std::string());
      out->proofBuffer << proofBuffer.rdbuf();
    }
  }

  template <typename S, typename L>
  std::unique_ptr<ConstrSimple<S, L>> toSimple_() const {
    std::unique_ptr<ConstrSimple<S, L>> result = std::make_unique<ConstrSimple<S, L>>();
    result->rhs = static_cast<L>(rhs);
    result->terms.reserve(vars.size());
    for (Var v : vars)
      if (coefs[v] != 0) result->terms.emplace_back(static_cast<S>(coefs[v]), v);
    if (global.logger.isActive()) result->proofLine = proofBuffer.str();
    result->orig = orig;
    return result;
  }
};

}  // namespace xct
