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

#include "parsing.hpp"
#include "Solver.hpp"

#if WITHCOINUTILS
#include "coin/CoinLpIO.hpp"
#include "coin/CoinMpsIO.hpp"
#endif

namespace rs::parsing {

bigint read_bigint(const std::string& s, int start) {
  int length = s.size();
  while (start < length && std::iswspace(s[start])) {
    ++start;
  }
  start += (start < length && s[start] == '+');
  bool negate = (start < length && s[start] == '-');
  bigint answer = 0;
  for (int i = start + negate; i < length; ++i) {
    char c = s[i];
    if ('0' <= c && c <= '9') {
      answer *= 10;
      answer += c - '0';
    } else {
      break;
    }
  }
  return negate ? -answer : answer;
}

void file_read(Solver& solver) {
  if (options.formulaName.empty()) {
    if (options.verbosity.get() > 0) {
      std::cout << "c No filename given, reading from standard input, expected format is " << options.fileFormat.get()
                << std::endl;
    }
  } else {
    std::string::size_type dotidx = options.formulaName.rfind('.');
    if (dotidx != std::string::npos) {
      std::string ext = options.formulaName.substr(dotidx + 1);
      if (options.fileFormat.valid(ext)) {
        options.fileFormat.parse(ext);
      }
    }
    if (options.verbosity.get() > 0) {
      std::cout << "c Reading input file, expected format is " << options.fileFormat.get() << std::endl;
    }
  }
  if (options.fileFormat.is("mps")) {
    mps_read(options.formulaName, solver);
  } else if (options.fileFormat.is("lp")) {
    lp_read(options.formulaName, solver);
  } else {
    if (options.formulaName.empty()) {
      if (options.fileFormat.is("opb")) {
        opb_read(std::cin, solver);
      } else if (options.fileFormat.is("cnf")) {
        cnf_read(std::cin, solver);
      } else if (options.fileFormat.is("wcnf")) {
        wcnf_read(std::cin, solver);
      } else {
        assert(false);
      }
    } else {
      std::ifstream fin(options.formulaName);
      if (!fin) quit::exit_ERROR({"Could not open ", options.formulaName});
      if (options.fileFormat.is("opb")) {
        opb_read(fin, solver);
      } else if (options.fileFormat.is("cnf")) {
        cnf_read(fin, solver);
      } else if (options.fileFormat.is("wcnf")) {
        wcnf_read(fin, solver);
      } else {
        assert(false);
      }
    }
  }
  if (logger) logger->logComment("INPUT FORMULA ABOVE - AUXILIARY AXIOMS BELOW");
}

void opb_read(std::istream& in, Solver& solver) {
  assert(!solver.hasObjective());
  ILP& ilp = solver.ilp;
  [[maybe_unused]] bool first_constraint = true;
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == '*') continue;
    for (char& c : line)
      if (c == ';') c = ' ';
    bool opt_line = line.substr(0, 4) == "min:";
    std::string line0;
    if (opt_line)
      line = line.substr(4), assert(first_constraint);
    else {
      std::string symbol;
      if (line.find(">=") != std::string::npos)
        symbol = ">=";
      else
        symbol = "=";
      assert(line.find(symbol) != std::string::npos);
      line0 = line;
      line = line.substr(0, line.find(symbol));
    }
    first_constraint = false;
    std::istringstream is(line);
    IntConstraint* input = ilp.newConstraint();
    std::vector<std::string> tokens;
    std::string tmp;
    while (is >> tmp) tokens.push_back(tmp);
    if (tokens.size() % 2 != 0) quit::exit_ERROR({"No support for non-linear constraints."});
    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      if (find(tokens[i].cbegin(), tokens[i].cend(), 'x') != tokens[i].cend()) {
        quit::exit_ERROR({"No support for non-linear constraints."});
      }
    }

    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      const std::string& var = tokens[i + 1];
      if (var.empty() || (var[0] != '~' && var[0] != 'x') || (var[0] == '~' && var[1] != 'x')) {
        quit::exit_ERROR({"Invalid literal token: ", var});
      }
      bool negated = (var[0] == '~');
      input->lhs.emplace_back(read_bigint(tokens[i], 0), ilp.getVarFor(var.substr(negated + 1)), negated);
    }
    if (opt_line) {
      ilp.obj = *input;
      ilp.constrs.pop_back();
    } else {
      input->setLowerBound(read_bigint(line0, line0.find('=') + 1));
      if (line0.find(" = ") != std::string::npos) input->setUpperBound(input->lowerBound);
    }
  }
  ilp.normalize(solver);
  ilp.addTo(solver, true);
}

void wcnf_read(std::istream& in, Solver& solver) {
  assert(!solver.hasObjective());
  ConstrSimple32 input;
  bigint top = -1;
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c') continue;
    if (line[0] == 'p') {
      assert(line.substr(0, 7) == "p wcnf ");
      solver.setNbVars(std::stoll(line.substr(7)), true);
      solver.maxSatVars = solver.getNbVars();
      bool nonWhitespace = false;
      for (int i = line.size() - 1; i >= 0; --i) {
        bool wspace = std::iswspace(line[i]);
        if (nonWhitespace && wspace) {
          top = read_bigint(line, i + 1);
          break;
        }
        nonWhitespace = nonWhitespace || !wspace;
      }
      assert(top >= 0);
    } else {
      assert(top >= 0);
      std::istringstream is(line);
      bigint weight;
      is >> weight;
      if (weight == 0) continue;
      if (weight < 0) {
        quit::exit_ERROR({"Negative clause weight: ", line});
      }
      input.reset();
      input.rhs = 1;
      Lit l;
      while (is >> l, l) {
        input.terms.push_back({1, l});
      }
      if (weight < top) {         // soft clause
        if (input.size() == 1) {  // no need to introduce auxiliary variable
          solver.objective->addLhs(weight, -input.terms[0].l);
        } else {
          Var aux = solver.getNbVars() + 1;
          solver.setNbVars(aux, true);  // increases n to n+1
          solver.objective->addLhs(weight, aux);
          if (options.test) {
            for (const Term<int>& t : input.terms) {  // reverse implication as binary clauses
              solver.addConstraintChecked(ConstrSimple32{{{1, -aux}, {1, -t.l}}, 1}, Origin::FORMULA);
            }
          } else {  // reverse implication as single constraint
            ConstrSimple32 reverse;
            reverse.rhs = input.size();
            reverse.terms.reserve(input.size() + 1);
            reverse.terms.push_back({input.size(), -aux});
            for (const Term<int>& t : input.terms) {
              reverse.terms.push_back({1, -t.l});
            }
            solver.addConstraintChecked(reverse, Origin::FORMULA);
          }
          input.terms.push_back({1, aux});
          solver.addConstraintChecked(input, Origin::FORMULA);  // implication
        }
      } else {  // hard clause
        solver.addConstraintChecked(input, Origin::FORMULA);
      }
      quit::checkInterrupt();
    }
  }
}

void cnf_read(std::istream& in, Solver& solver) {
  ConstrSimple32 input;
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c' || line[0] == 'p') continue;
    std::istringstream is(line);
    input.reset();
    input.rhs = 1;
    Lit l;
    while (is >> l, l) {
      solver.setNbVars(std::abs(l), true);
      input.terms.push_back({1, l});
    }
    solver.addConstraintChecked(input, Origin::FORMULA);
    quit::checkInterrupt();
  }
}

#if WITHCOINUTILS
bigint lcm(const bigint& x, const bigint& y) {
  assert(x != 0);
  return y == 0 ? x : boost::multiprecision::lcm(x, y);
}

bigint scaleToIntegers(IntConstraint& ic) {
  namespace mult = boost::multiprecision;

  bigint multiplier = 1;
  for (IntTerm& t : ic.lhs) {
    multiplier = lcm(multiplier, mult::denominator(t.c));
  }
  if (ic.lowerBoundSet) {
    multiplier = lcm(multiplier, mult::denominator(ic.lowerBound));
  }
  if (ic.upperBoundSet) {
    multiplier = lcm(multiplier, mult::denominator(ic.upperBound));
  }

  for (IntTerm& t : ic.lhs) {
    t.c *= multiplier;
    assert(mult::denominator(t.c) == 1);
  }
  if (ic.lowerBoundSet) {
    ic.lowerBound *= multiplier;
    assert(mult::denominator(ic.lowerBound) == 1);
  }
  if (ic.upperBoundSet) {
    ic.upperBound *= multiplier;
    assert(mult::denominator(ic.upperBound) == 1);
  }
  return multiplier;
}

template <typename T>
void coinutils_read(T& coinutils, Solver& solver, bool wasMaximization) {
  ILP& ilp = solver.ilp;

  bool continuousVars = false;
  bool unboundedVars = false;
  for (int c = 0; c < coinutils.getNumCols(); ++c) {
    continuousVars = continuousVars || !coinutils.isInteger(c);
    IntVar* iv = ilp.getVarFor(coinutils.columnName(c));
    double lower = coinutils.getColLower()[c];
    if (aux::abs(lower) == coinutils.getInfinity()) {
      unboundedVars = true;
      lower = -options.intDefaultBound.get();
    }
    iv->lowerBound = static_cast<bigint>(std::ceil(lower));
    double upper = coinutils.getColUpper()[c];
    if (aux::abs(upper) == coinutils.getInfinity()) {
      unboundedVars = true;
      upper = options.intDefaultBound.get();
    }
    iv->upperBound = static_cast<bigint>(std::floor(upper));
  }
  if (continuousVars) std::cout << "c WARNING continuous variables are treated as integer variables" << std::endl;
  if (unboundedVars)
    std::cout << "c WARNING unbounded variables have custom bounds of +-" << options.intDefaultBound.get() << std::endl;

  for (int c = 0; c < coinutils.getNumCols(); ++c) {
    double objcoef = coinutils.getObjCoefficients()[c];
    if (objcoef == 0) continue;
    ilp.obj.lhs.emplace_back(objcoef, ilp.getVarFor(coinutils.columnName(c)), false);
  }
  if (wasMaximization) {
    ilp.obj.setLowerBound(coinutils.objectiveOffset());
    ilp.objmult = -1;
  } else {
    ilp.obj.setLowerBound(-coinutils.objectiveOffset());
  }
  ilp.objmult *= scaleToIntegers(ilp.obj);

  const CoinPackedMatrix* cpm = coinutils.getMatrixByRow();
  for (int r = 0; r < coinutils.getNumRows(); ++r) {
    quit::checkInterrupt();
    char rowSense = coinutils.getRowSense()[r];
    if (rowSense == 'N') continue;  // free constraint
    IntConstraint* input = ilp.newConstraint();
    input->lhs.reserve(cpm->getVectorLengths()[r]);
    for (int c = cpm->getVectorFirst(r); c < cpm->getVectorLast(r); ++c) {
      input->lhs.emplace_back(cpm->getElements()[c], ilp.getVarFor(coinutils.columnName(cpm->getIndices()[c])), false);
    }
    if (rowSense == 'G' || rowSense == 'E' || rowSense == 'R') {
      input->setLowerBound(coinutils.getRowLower()[r]);
    }
    if (rowSense == 'L' || rowSense == 'E' || rowSense == 'R') {
      input->setUpperBound(coinutils.getRowUpper()[r]);
    }
    scaleToIntegers(*input);
  }

  ilp.normalize(solver);
  ilp.addTo(solver, false);
}

template void coinutils_read<CoinMpsIO>(CoinMpsIO& coinutils, Solver& solver, bool wasMaximization);
template void coinutils_read<CoinLpIO>(CoinLpIO& coinutils, Solver& solver, bool wasMaximization);

void mps_read(const std::string& filename, Solver& solver) {
  CoinMpsIO coinutils;
  coinutils.messageHandler()->setLogLevel(0);
  if (filename == "") {
    coinutils.readMps("-");  // NOTE: filename "-" reads from stdin
  } else {
    coinutils.readMps(filename.c_str(), "");
  }
  coinutils_read<CoinMpsIO>(coinutils, solver, false);
}

void lp_read(const std::string& filename, Solver& solver) {
  CoinLpIO coinutils;
  coinutils.messageHandler()->setLogLevel(0);
  if (filename == "") {
    coinutils.readLp(stdin);
  } else {
    coinutils.readLp(filename.c_str());
  }
  coinutils_read<CoinLpIO>(coinutils, solver, coinutils.wasMaximization());
}

#else
void mps_read([[maybe_unused]] const std::string& filename, [[maybe_unused]] Solver& solver) {
  quit::exit_ERROR({"Please compile with CoinUtils to parse MPS format."});
}

void lp_read([[maybe_unused]] const std::string& filename, [[maybe_unused]] Solver& solver) {
  quit::exit_ERROR({"Please compile with CoinUtils to parse LP format."});
}
#endif

std::ostream& operator<<(std::ostream& o, const IntVar& x) {
  o << x.name;
  if (!x.isBoolean()) {
    o << "[" << x.lowerBound << "," << x.upperBound << "]";
  }
  return o;
}
std::ostream& operator<<(std::ostream& o, const IntTerm& x) { return o << x.c << (x.negated ? "~x" : "x") << *x.v; }
std::ostream& operator<<(std::ostream& o, const IntConstraint& x) {
  if (x.upperBoundSet) o << x.upperBound << " >= ";
  for (const IntTerm& t : x.lhs) o << t << " ";
  if (x.lowerBoundSet) o << " >= " << x.lowerBound;
  return o;
}
std::ostream& operator<<(std::ostream& o, const ILP& x) {
  o << "obj: " << x.obj;
  for (const std::unique_ptr<IntConstraint>& c : x.constrs) o << "\n" << *c;
  return o;
}

void IntConstraint::toConstrExp(CeArb& input, bool useLowerBound) const {
  if (useLowerBound) {
    assert(boost::multiprecision::denominator(lowerBound) == 1);
    input->addRhs(boost::multiprecision::numerator(lowerBound));
  } else {
    assert(boost::multiprecision::denominator(upperBound) == 1);
    input->addRhs(boost::multiprecision::numerator(upperBound));
  }
  for (const IntTerm& t : lhs) {
    assert(!t.negated);
    assert(t.v->lowerBound == 0);
    assert(t.v->upperBound >= 0);
    if (t.v->upperBound == 0) continue;
    assert(!t.v->encoding.empty());
    if (t.v->logEncoding) {
      bigint base = 1;
      for (const Var v : t.v->encoding) {
        assert(boost::multiprecision::denominator(t.c) == 1);
        input->addLhs(base * boost::multiprecision::numerator(t.c), v);
        base *= 2;
      }
    } else {
      for (const Var v : t.v->encoding) {
        assert(boost::multiprecision::denominator(t.c) == 1);
        input->addLhs(boost::multiprecision::numerator(t.c), v);
      }
    }
  }
  if (!useLowerBound) input->invert();
}

void IntConstraint::normalize() {
  for (IntTerm& t : lhs) {
    if (t.negated) {
      assert(t.v->isBoolean());
      t.c = -t.c;
      if (lowerBoundSet) lowerBound += t.c;
      if (upperBoundSet) upperBound += t.c;
      t.negated = false;
    } else if (t.v->lowerBound != 0) {
      RatVal adjustment = -t.c * t.v->lowerBound;
      if (lowerBoundSet) lowerBound += adjustment;
      if (upperBoundSet) upperBound += adjustment;
    }
  }
}

IntVar* ILP::getVarFor(const std::string& name) {
  if (name2var.count(name)) return name2var[name];
  vars.push_back(std::make_unique<IntVar>(name));
  IntVar* result = vars.back().get();
  name2var.insert({name, result});
  return result;
}

IntConstraint* ILP::newConstraint() {
  constrs.push_back(std::make_unique<IntConstraint>());
  return constrs.back().get();
}

void ILP::addTo(Solver& solver, bool nameAsId) {
  if (nameAsId) {
    for (const std::unique_ptr<IntVar>& iv : vars) {
      assert(iv->isBoolean());
      Var next = std::stoi(iv->name);
      solver.setNbVars(next, true);
      iv->encoding.push_back(next);
    }
  } else {
    for (const std::unique_ptr<IntVar>& iv : vars) {
      assert(iv->lowerBound == 0);
      assert(iv->upperBound >= 0);
      if (iv->upperBound == 0) continue;
      bigint range = iv->getRange();
      iv->logEncoding = range > options.intEncoding.get();
      int newvars = iv->logEncoding ? aux::msb(range) + 1 : static_cast<int>(range);
      int oldvars = solver.getNbVars();
      solver.setNbVars(oldvars + newvars, true);
      for (Var var = oldvars + 1; var <= oldvars + newvars; ++var) {
        iv->encoding.push_back(var);
      }
      if (iv->logEncoding) {  // upper bound constraint
        std::vector<Term<bigint>> lhs;
        lhs.reserve(iv->encoding.size());
        bigint base = 1;
        for (const Var v : iv->encoding) {
          lhs.emplace_back(-base, v);
          base *= 2;
        }
        solver.addConstraintChecked(ConstrSimpleArb({lhs}, -iv->upperBound), Origin::FORMULA);
        quit::checkInterrupt();
      } else {  // binary order constraints
        for (Var var = oldvars + 1; var < oldvars + newvars; ++var) {
          solver.addConstraintChecked(ConstrSimple32({{1, var}, {1, -var - 1}}, 1), Origin::FORMULA);
          quit::checkInterrupt();
        }
      }
    }
  }
  obj.toConstrExp(solver.objective, true);
  CeArb input = cePools.takeArb();
  for (const std::unique_ptr<IntConstraint>& c : constrs) {
    if (c->lowerBoundSet) {
      c->toConstrExp(input, true);
      solver.addConstraintChecked(input, Origin::FORMULA);
      quit::checkInterrupt();
      input->reset(false);
    }
    if (c->upperBoundSet) {
      c->toConstrExp(input, false);
      solver.addConstraintChecked(input, Origin::FORMULA);
      quit::checkInterrupt();
      input->reset(false);
    }
  }
}

/**
 * remove negated terms
 * get lower bounds to 0
 * turn all constraints in GTE or EQ
 */
void ILP::normalize(Solver& solver) {
  obj.normalize();
  for (std::unique_ptr<IntConstraint>& c : constrs) {
    c->normalize();
  }
  for (const std::unique_ptr<IntVar>& iv : vars) {
    if (iv->lowerBound != 0) {
      iv->offset = iv->lowerBound;
      iv->upperBound -= iv->lowerBound;
      iv->lowerBound = 0;
    }
    if (iv->upperBound < 0) {
      std::cout << "Conflicting bound on integer variable" << std::endl;
      quit::exit_SUCCESS(solver);
    }
  }
}

void ILP::printOrigSol(const std::vector<Lit>& sol) {
  std::unordered_set<Var> trueVars;
  for (Lit l : sol) {
    if (l > 0) {
      trueVars.insert(l);
    }
  }
  for (const std::unique_ptr<IntVar>& iv : vars) {
    bigint val = iv->offset;
    if (iv->logEncoding) {
      bigint base = 1;
      for (Var v : iv->encoding) {
        if (trueVars.count(v)) {
          val += base;
        }
        base *= 2;
      }
    } else {
      int sum = 0;
      for (Var v : iv->encoding) {
        sum += trueVars.count(v);
      }
      val += sum;
    }
    if (val != 0) {
      std::cout << iv->name << " " << val << "\n";
    }
  }
}

}  // namespace rs::parsing
