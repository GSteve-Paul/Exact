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
#include "ILP.hpp"
#include "Solver.hpp"

#if WITHCOINUTILS
#include "coin/CoinLpIO.hpp"
#include "coin/CoinMpsIO.hpp"
#endif

namespace xct::parsing {

// TODO: check efficiency of parsing with a .opb-file that takes long to parse, according to experiments

bigint read_bigint(const std::string& s, int start) {
  int length = s.size();
  while (start < length && iswspace(s[start])) {
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

void file_read(ILP& ilp) {
  if (ilp.global.options.formulaName.empty()) {
    if (ilp.global.options.verbosity.get() > 0) {
      std::cout << "c No filename given, reading from standard input, expected format is "
                << ilp.global.options.fileFormat.get() << std::endl;
    }
  } else {
    std::string::size_type dotidx = ilp.global.options.formulaName.rfind('.');
    if (dotidx != std::string::npos) {
      std::string ext = ilp.global.options.formulaName.substr(dotidx + 1);
      if (ilp.global.options.fileFormat.valid(ext)) {
        ilp.global.options.fileFormat.parse(ext);
      }
    }
    if (ilp.global.options.verbosity.get() > 0) {
      std::cout << "c Reading input file, expected format is " << ilp.global.options.fileFormat.get() << std::endl;
    }
  }
  if (ilp.global.options.fileFormat.is("mps")) {
    mps_read(ilp.global.options.formulaName, ilp);
  } else if (ilp.global.options.fileFormat.is("lp")) {
    lp_read(ilp.global.options.formulaName, ilp);
  } else {
    if (ilp.global.options.formulaName.empty()) {
      if (ilp.global.options.fileFormat.is("opb")) {
        opb_read(std::cin, ilp);
      } else if (ilp.global.options.fileFormat.is("cnf")) {
        cnf_read(std::cin, ilp);
      } else if (ilp.global.options.fileFormat.is("wcnf")) {
        wcnf_read(std::cin, ilp);
      } else {
        assert(false);
      }
    } else {
      std::ifstream fin(ilp.global.options.formulaName);
      if (!fin) quit::exit_ERROR({"Could not open ", ilp.global.options.formulaName});
      if (ilp.global.options.fileFormat.is("opb")) {
        opb_read(fin, ilp);
      } else if (ilp.global.options.fileFormat.is("cnf")) {
        cnf_read(fin, ilp);
      } else if (ilp.global.options.fileFormat.is("wcnf")) {
        wcnf_read(fin, ilp);
      } else {
        assert(false);
      }
      fin.close();
    }
  }
  ilp.global.logger.logComment("INPUT FORMULA ABOVE - AUXILIARY AXIOMS BELOW");
}

void opb_read(std::istream& in, ILP& ilp) {
  [[maybe_unused]] bool first_constraint = true;
  std::vector<bigint> coefs;
  std::vector<IntVar*> vars;
  std::vector<bool> negated;
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == '*') continue;
    for (char& c : line)
      if (c == ';') c = ' ';
    bool opt_line = line.substr(0, 4) == "min:";
    bigint lb;
    bool isInequality = false;
    if (opt_line) {
      line = line.substr(4), assert(first_constraint);
      if (std::all_of(line.begin(), line.end(), isspace)) {
        quit::exit_ERROR({"Empty objective function."});
      }
    } else {
      size_t eqpos = line.find('=');
      if (eqpos == std::string::npos || eqpos == 0) {
        quit::exit_ERROR({"Incorrect constraint\n" + line});
      }
      lb = read_bigint(line, eqpos + 1);
      isInequality = line[eqpos - 1] == '>';
      line = line.substr(0, eqpos - isInequality);
    }
    first_constraint = false;
    std::istringstream is(line);

    std::vector<std::string> tokens;
    std::string tmp;
    while (is >> tmp) tokens.push_back(tmp);
    if (tokens.size() % 2 != 0) quit::exit_ERROR({"No support for non-linear constraints."});
    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      if (find(tokens[i].cbegin(), tokens[i].cend(), 'x') != tokens[i].cend()) {
        quit::exit_ERROR({"No support for non-linear constraints."});
      }
    }

    coefs.clear();
    vars.clear();
    negated.clear();
    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      const std::string& var = tokens[i + 1];
      if (var.empty() || (var[0] != '~' && var[0] != 'x') || (var[0] == '~' && var[1] != 'x')) {
        quit::exit_ERROR({"Invalid literal token: ", var});
      }
      coefs.emplace_back(read_bigint(tokens[i], 0));
      negated.emplace_back(var[0] == '~');
      vars.emplace_back(ilp.getVarFor(var.substr(negated.back() + 1)));
    }

    if (opt_line) {
      ilp.setObjective(coefs, vars, negated);
    } else {
      State res = ilp.addConstraint(coefs, vars, negated, lb, aux::option(!isInequality, lb));
      if (res == State::UNSAT) quit::exit_SUCCESS(ilp);
    }
  }
}

void wcnf_read(std::istream& in, ILP& ilp) {
  std::vector<ConstrSimple32> inputs;
  char dummy;
  std::vector<bigint> objcoefs;
  std::vector<IntVar*> objvars;
  std::vector<bool> objnegated;
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c') continue;
    quit::checkInterrupt(ilp.global);
    std::istringstream is(line);
    bigint weight = 0;
    if (line[0] == 'h') {
      is >> dummy;
    } else {
      is >> weight;
      if (weight == 0) continue;
      if (weight < 0) {
        quit::exit_ERROR({"Negative clause weight: ", line});
      }
    };
    inputs.emplace_back();
    ConstrSimple32& input = inputs.back();
    input.rhs = 1;
    objcoefs.push_back(weight);
    Lit l;
    while (is >> l, l) {
      input.terms.push_back({1, l});
      ilp.getSolver().setNbVars(toVar(l), true);
    }
    if (weight == 0) {  // hard clause
      if (ilp.getSolver().addConstraint(input, Origin::FORMULA).second == ID_Unsat) quit::exit_SUCCESS(ilp);
      inputs.pop_back();
      objcoefs.pop_back();
    }
  }
  ilp.setMaxSatVars();
  assert(inputs.size() == objcoefs.size());
  for (ConstrSimple32& input : inputs) {  // soft clauses
    quit::checkInterrupt(ilp.global);
    if (input.size() == 1) {  // no need to introduce auxiliary variable
      objvars.push_back(ilp.getVarFor(std::to_string(toVar(input.terms[0].l)), true));
      objnegated.push_back(-input.terms[0].l < 0);
    } else {
      Var aux = ilp.getSolver().getNbVars() + 1;
      ilp.getSolver().setNbVars(aux, true);  // increases n to n+1
      objvars.push_back(ilp.getVarFor(std::to_string(toVar(aux)), true));
      objnegated.push_back(aux < 0);
      // if (ilp.global.options.test.get()) {
      for (const Term32& t : input.terms) {  // reverse implication as binary clauses
        if (ilp.getSolver().addConstraint(ConstrSimple32{{{1, -aux}, {1, -t.l}}, 1}, Origin::FORMULA).second ==
            ID_Unsat)
          quit::exit_SUCCESS(ilp);
      }
      //} else {  // reverse implication as single constraint // TODO: add this one constraint instead?
      //        ConstrSimple32 reverse;
      //        reverse.rhs = input.size();
      //        reverse.terms.reserve(input.size() + 1);
      //        reverse.terms.push_back({(int) input.size(), -aux});
      //        for (const Term32& t : input.terms) {
      //          reverse.terms.push_back({1, -t.l});
      //        }
      //        if (ilp.getSolver().addConstraint(input, Origin::FORMULA).second == ID_Unsat) quit::exit_SUCCESS(ilp);
      //}
      input.terms.push_back({1, aux});  // implication
      if (ilp.getSolver().addConstraint(input, Origin::FORMULA).second == ID_Unsat) quit::exit_SUCCESS(ilp);
    }
  }
  ilp.setObjective(objcoefs, objvars, objnegated);
}

void cnf_read(std::istream& in, ILP& ilp) {
  ConstrSimple32 input;
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c' || line[0] == 'p') continue;
    std::istringstream is(line);
    input.reset();
    input.rhs = 1;
    Lit l;
    while (is >> l, l) {
      ilp.getSolver().setNbVars(toVar(l), true);
      input.terms.push_back({1, l});
    }
    if (ilp.getSolver().addConstraint(input, Origin::FORMULA).second == ID_Unsat) quit::exit_SUCCESS(ilp);
    quit::checkInterrupt(ilp.global);
  }
}

#if WITHCOINUTILS
bigint lcm(const bigint& x, const bigint& y) {
  assert(x != 0);
  return y == 0 ? x : boost::multiprecision::lcm(x, y);
}

template <typename T>
void coinutils_read(T& coinutils, ILP& ilp, bool wasMaximization) {
  // Variables
  bool continuousVars = false;
  bool unboundedVars = false;
  for (int c = 0; c < coinutils.getNumCols(); ++c) {
    quit::checkInterrupt(ilp.global);
    continuousVars = continuousVars || !coinutils.isInteger(c);
    double lower = coinutils.getColLower()[c];
    if (aux::abs(lower) == coinutils.getInfinity()) {
      unboundedVars = true;
      lower = -ilp.global.options.intDefaultBound.get();
    }
    double upper = coinutils.getColUpper()[c];
    if (aux::abs(upper) == coinutils.getInfinity()) {
      unboundedVars = true;
      upper = ilp.global.options.intDefaultBound.get();
    }
    if (upper < lower) {
      std::cout << "Conflicting bound on integer variable" << std::endl;
      quit::exit_SUCCESS(ilp);
    }
    [[maybe_unused]] IntVar* iv = ilp.getVarFor(coinutils.columnName(c), false, static_cast<bigint>(std::ceil(lower)),
                                                static_cast<bigint>(std::floor(upper)));
  }
  if (continuousVars) std::cout << "c WARNING continuous variables are treated as integer variables" << std::endl;
  if (unboundedVars) {
    std::cout << "c WARNING unbounded integer variables have custom bounds of +-"
              << ilp.global.options.intDefaultBound.get() << std::endl;
  }

  std::vector<ratio> ratcoefs;
  std::vector<bigint> coefs;
  std::vector<IntVar*> vars;

  // Objective
  for (int c = 0; c < coinutils.getNumCols(); ++c) {
    double objcoef = coinutils.getObjCoefficients()[c];
    if (objcoef == 0) continue;
    ratcoefs.emplace_back(objcoef);
    vars.emplace_back(ilp.getVarFor(coinutils.columnName(c)));
  }
  ratcoefs.emplace_back(coinutils.objectiveOffset());
  bigint cdenom = aux::commonDenominator(ratcoefs);
  for (const ratio& r : ratcoefs) {
    coefs.emplace_back(r * cdenom);
  }
  bigint offset = coefs.back();
  coefs.pop_back();
  if (wasMaximization) {
    cdenom = -cdenom;
    offset = -offset;
  }
  ilp.setObjective(coefs, vars, {}, cdenom, offset);

  // Constraints
  const CoinPackedMatrix* cpm = coinutils.getMatrixByRow();
  for (int r = 0; r < coinutils.getNumRows(); ++r) {
    quit::checkInterrupt(ilp.global);
    char rowSense = coinutils.getRowSense()[r];
    if (rowSense == 'N') continue;  // free constraint

    ratcoefs.clear();
    coefs.clear();
    vars.clear();
    for (int c = cpm->getVectorFirst(r); c < cpm->getVectorLast(r); ++c) {
      double coef = cpm->getElements()[c];
      if (coef == 0) continue;
      ratcoefs.emplace_back(coef);
      vars.emplace_back(ilp.getVarFor(coinutils.columnName(cpm->getIndices()[c])));
    }
    bool useLB = rowSense == 'G' || rowSense == 'E' || rowSense == 'R';
    ratcoefs.emplace_back(useLB ? coinutils.getRowLower()[r] : 0);
    bool useUB = rowSense == 'L' || rowSense == 'E' || rowSense == 'R';
    ratcoefs.emplace_back(useUB ? coinutils.getRowUpper()[r] : 0);
    bigint cdenom = aux::commonDenominator(ratcoefs);
    for (const ratio& r : ratcoefs) {
      coefs.emplace_back(r * cdenom);
    }
    bigint ub = coefs.back();
    coefs.pop_back();
    bigint lb = coefs.back();
    coefs.pop_back();
    State res = ilp.addConstraint(coefs, vars, {}, aux::option(useLB, lb), aux::option(useUB, ub));
    if (res == State::UNSAT) quit::exit_SUCCESS(ilp);
  }
}

template void coinutils_read<CoinMpsIO>(CoinMpsIO& coinutils, ILP& ilp, bool wasMaximization);
template void coinutils_read<CoinLpIO>(CoinLpIO& coinutils, ILP& ilp, bool wasMaximization);

void mps_read(const std::string& filename, ILP& ilp) {
  CoinMpsIO coinutils;
  coinutils.messageHandler()->setLogLevel(0);
  if (filename == "") {
    coinutils.readMps("-");  // NOTE: filename "-" reads from stdin
  } else {
    coinutils.readMps(filename.c_str(), "");
  }
  coinutils_read<CoinMpsIO>(coinutils, ilp, false);
}

void lp_read(const std::string& filename, ILP& ilp) {
  CoinLpIO coinutils;
  coinutils.messageHandler()->setLogLevel(0);
  if (filename == "") {
    coinutils.readLp(stdin);
  } else {
    coinutils.readLp(filename.c_str());
  }
  coinutils_read<CoinLpIO>(coinutils, ilp, coinutils.wasMaximization());
}

#else
void mps_read([[maybe_unused]] const std::string& filename, [[maybe_unused]] ILP& ilp) {
  quit::exit_ERROR({"Please compile with CoinUtils to parse MPS format."});
}

void lp_read([[maybe_unused]] const std::string& filename, [[maybe_unused]] ILP& ilp) {
  quit::exit_ERROR({"Please compile with CoinUtils to parse LP format."});
}
#endif

}  // namespace xct::parsing
