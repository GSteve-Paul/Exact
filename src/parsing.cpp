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

#include "parsing.hpp"
#include <boost/algorithm/string/replace.hpp>
#include <boost/tokenizer.hpp>
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
      if (!fin) {
        throw InvalidArgument("Could not open " + ilp.global.options.formulaName);
      }
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

IntVar* indexedBoolVar(ILP& ilp, const std::string& name) {
  if (IntVar* res = ilp.getVarFor(name); res) return res;
  return ilp.addVar(name, 0, 1, Encoding::ORDER, true);
}

void opb_read(std::istream& in, ILP& ilp) {
  [[maybe_unused]] bool first_constraint = true;
  std::vector<IntTerm> terms;
  bigint lb;
  long long lineNr = -1;
  for (std::string line; getline(in, line);) {
    ++lineNr;
    if (line.empty() || line[0] == '*') continue;
    for (char& c : line) {
      if (c == ';') c = ' ';
    }
    bool opt_line = line.substr(0, 4) == "min:";
    lb = 0;
    bool isInequality = false;
    if (opt_line) {
      assert(first_constraint);
      line = line.substr(4);
      if (std::all_of(line.begin(), line.end(), isspace)) {
        std::cout << "c WARNING objective function is empty" << std::endl;
        // TODO: global warning routine that also checks for verbosity
      }
    } else {
      size_t eqpos = line.find('=');
      if (eqpos == std::string::npos || eqpos == 0) {
        throw InvalidArgument("Incorrect constraint at line " + std::to_string(lineNr) + ":\n" + line);
      }
      lb += read_bigint(line, eqpos + 1);
      isInequality = line[eqpos - 1] == '>';
      line = line.substr(0, eqpos - isInequality);
    }
    first_constraint = false;
    std::istringstream is(line);

    std::vector<std::string> tokens;
    std::string tmp;
    while (is >> tmp) tokens.push_back(tmp);
    if (tokens.size() % 2 != 0) {
      throw InvalidArgument("No support for non-linear constraint at line " + std::to_string(lineNr));
    }
    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      if (find(tokens[i].cbegin(), tokens[i].cend(), 'x') != tokens[i].cend()) {
        throw InvalidArgument("No support for non-linear constraint at line " + std::to_string(lineNr));
      }
    }

    terms.clear();
    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      const std::string& var = tokens[i + 1];
      if (var.empty()) {
        throw InvalidArgument("Invalid literal token " + var + " at line " + std::to_string(lineNr));
      } else if (var[0] == '~') {
        terms.push_back({-read_bigint(tokens[i], 0), indexedBoolVar(ilp, var.substr(2))});
        lb += terms.back().c;
      } else if (var[0] == 'x') {
        terms.push_back({read_bigint(tokens[i], 0), indexedBoolVar(ilp, var.substr(1))});
      } else {
        lb -= read_bigint(tokens[i], 0) * read_bigint(var, 0);
      }
    }

    if (opt_line) {
      ilp.setObjective(terms, -lb);
    } else {
      ilp.addConstraint(IntConstraint{terms, lb, aux::option(!isInequality, lb)});
    }
  }
}

void wcnf_read(std::istream& in, ILP& ilp) {
  std::vector<ConstrSimple32> inputs;
  char dummy;
  std::vector<IntTerm> obj_terms;
  bigint obj_offset = 0;
  // NOTE: there are annoying edge cases where two clauses share the same line, or a clause is split on two lines.
  // the following rewrite fixes this.
  std::string all = "";
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c') continue;
    if (line[0] == '0') line[0] = '#';
    all += boost::replace_all_copy(line, " 0", "#");
  }
  boost::tokenizer<boost::char_separator<char>> lines(all, boost::char_separator<char>("#"));
  for (const std::string& line : lines) {
    std::istringstream is(line);
    bigint weight = 0;
    if (line[0] == 'h') {
      is >> dummy;
    } else {
      is >> weight;
      if (weight <= 0) {
        throw InvalidArgument("Non-positive clause weight: " + line);
      }
    }
    inputs.emplace_back();
    ConstrSimple32& input = inputs.back();
    input.rhs = 1;
    obj_terms.push_back({weight, nullptr});
    Lit l = 0;
    while (is >> l) {
      input.terms.push_back({1, l});
      ilp.getSolver().setNbVars(toVar(l), true);
    }
    if (weight == 0) {  // hard clause
      ilp.getSolver().addConstraint(input, Origin::FORMULA);
      inputs.pop_back();
      obj_terms.pop_back();
    }
  }
  ilp.setMaxSatVars();
  // NOTE: to avoid using original maxsat variable indices for auxiliary variables,
  // introduce auxiliary variables *after* parsing all the original maxsat variables
  assert(inputs.size() == obj_terms.size());
  for (int64_t i = inputs.size() - 1; i >= 0; --i) {
    quit::checkInterrupt(ilp.global);
    assert(i + 1 == (int64_t)inputs.size());  // each processed input is popped
    ConstrSimple32& input = inputs[i];
    if (input.size() == 1) {  // no need to introduce auxiliary variable
      Lit ll = input.terms[0].l;
      obj_terms[i].v = indexedBoolVar(ilp, std::to_string(toVar(ll)));
      if (ll > 0) {
        const bigint& weight = obj_terms[i].c;
        obj_offset += weight;
        obj_terms[i].c = -weight;
      }
    } else {
      Var aux = ilp.getSolver().addVar(true);
      ilp.getSolver().setNbVars(aux, true);  // increases n to n+1
      obj_terms[i].v = indexedBoolVar(ilp, std::to_string(toVar(aux)));
      for (const Term32& t : input.terms) {  // reverse implication as binary clauses
        ilp.getSolver().addBinaryConstraint(-aux, -t.l, Origin::FORMULA);
      }
      input.terms.push_back({1, aux});  // implication
      ilp.getSolver().addConstraint(input, Origin::FORMULA);
    }
    inputs.pop_back();
  }
  ilp.setObjective(obj_terms, obj_offset);
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
    ilp.getSolver().addConstraint(input, Origin::FORMULA);
    quit::checkInterrupt(ilp.global);
  }
}

#if WITHCOINUTILS
bigint lcm(const bigint& x, const bigint& y) {
  assert(x != 0);
  return y == 0 ? x : boost::multiprecision::lcm(x, y);
}

ratio parseCoinUtilsFloat(double x, bool& firstFloat) {
  if (firstFloat && std::floor(x) != x) {
    std::cout << "c WARNING floating point values may not be exactly represented by double" << std::endl;
    firstFloat = false;
  }
  return static_cast<ratio>(x);
}

template <typename T>
void coinutils_read(T& coinutils, ILP& ilp, bool wasMaximization) {
  // Variables
  for (int c = 0; c < coinutils.getNumCols(); ++c) {
    quit::checkInterrupt(ilp.global);
    const std::string varname = coinutils.columnName(c);
    if (!coinutils.isInteger(c)) {
      if (ilp.global.options.ilpContinuous) {
        std::cout << "c WARNING continuous variable " << varname << " treated as integer" << std::endl;
      } else {
        throw InvalidArgument("No support for continuous variables: " + varname);
      }
    }
    double lower = coinutils.getColLower()[c];
    if (aux::abs(lower) == coinutils.getInfinity()) {
      if (ilp.global.options.ilpUnbounded) {
        lower = -ilp.global.options.ilpDefaultBound.get();
        std::cout << "c WARNING default lower bound " << lower << " for unbounded variable " << varname << std::endl;
      } else {
        throw InvalidArgument("No support for unbounded variables: " + varname);
      }
    }
    double upper = coinutils.getColUpper()[c];
    if (aux::abs(upper) == coinutils.getInfinity()) {
      if (ilp.global.options.ilpUnbounded) {
        upper = ilp.global.options.ilpDefaultBound.get();
        std::cout << "c WARNING default upper bound " << upper << " for unbounded variable " << varname << std::endl;
      } else {
        throw InvalidArgument("No support for unbounded variables: " + varname);
      }
    }
    if (std::ceil(upper) < std::floor(upper)) {
      std::cout << "c Conflicting bound on integer variable" << std::endl;
      ilp.addConstraint(IntConstraint{{}, {}, 1});  // 0>=1 should trigger UNSAT
    }
    [[maybe_unused]] IntVar* iv =
        ilp.addVar(varname, static_cast<bigint>(std::ceil(lower)), static_cast<bigint>(std::floor(upper)),
                   opt2enc(ilp.global.options.ilpEncoding.get()));
  }

  std::vector<ratio> ratcoefs;
  std::vector<bigint> coefs;
  std::vector<IntVar*> vars;
  bool firstFloat = true;

  // Objective
  for (int c = 0; c < coinutils.getNumCols(); ++c) {
    double objcoef = coinutils.getObjCoefficients()[c];
    if (objcoef == 0) continue;
    ratcoefs.emplace_back(parseCoinUtilsFloat(objcoef, firstFloat));
    vars.emplace_back(ilp.getVarFor(coinutils.columnName(c)));
  }
  ratcoefs.emplace_back(parseCoinUtilsFloat(coinutils.objectiveOffset(), firstFloat));
  bigint cdenom = aux::commonDenominator(ratcoefs);
  if (wasMaximization) {
    cdenom = -cdenom;
  }
  for (const ratio& r : ratcoefs) {
    coefs.emplace_back(r * cdenom);
  }
  bigint offset = coefs.back();
  coefs.pop_back();
  ilp.setObjective(IntConstraint::zip(coefs, vars), offset);

  // Constraints
  const CoinPackedMatrix* cpm = coinutils.getMatrixByRow();
  if (cpm == nullptr) throw InvalidArgument("CoinUtils parsing failed.");
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
      ratcoefs.emplace_back(parseCoinUtilsFloat(coef, firstFloat));
      vars.emplace_back(ilp.getVarFor(coinutils.columnName(cpm->getIndices()[c])));
    }
    bool useLB = rowSense == 'G' || rowSense == 'E' || rowSense == 'R';
    ratcoefs.emplace_back(useLB ? parseCoinUtilsFloat(coinutils.getRowLower()[r], firstFloat) : 0);
    bool useUB = rowSense == 'L' || rowSense == 'E' || rowSense == 'R';
    ratcoefs.emplace_back(useUB ? parseCoinUtilsFloat(coinutils.getRowUpper()[r], firstFloat) : 0);
    bigint cdenom = aux::commonDenominator(ratcoefs);
    for (const ratio& rat : ratcoefs) {
      coefs.emplace_back(rat * cdenom);
    }
    bigint ub = coefs.back();
    coefs.pop_back();
    bigint lb = coefs.back();
    coefs.pop_back();
    ilp.addConstraint({IntConstraint::zip(coefs, vars), aux::option(useLB, lb), aux::option(useUB, ub)});
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
  throw InvalidArgument("Please compile with CoinUtils to parse MPS format.");
}

void lp_read([[maybe_unused]] const std::string& filename, [[maybe_unused]] ILP& ilp) {
  throw InvalidArgument("Please compile with CoinUtils to parse LP format.");
}
#endif

}  // namespace xct::parsing
