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

#include "auxiliary.hpp"
#include "quit.hpp"
#include "used_licenses/licenses.hpp"

namespace xct {

class Option {
 public:
  const std::string name;
  const std::string description;

  Option(const std::string& n, const std::string& d) : name(n), description(d) {}

  virtual void printUsage(int colwidth) const = 0;
  virtual void parse(const std::string& v) = 0;
};

class VoidOption : public Option {
  bool val = false;

 public:
  VoidOption(const std::string& n, const std::string& d);

  explicit operator bool() const { return val; }

  void printUsage(int colwidth) const override;
  void parse([[maybe_unused]] const std::string& v) override;
};

class BoolOption : public Option {
  bool val = false;

 public:
  BoolOption(const std::string& n, const std::string& d, bool v);

  explicit operator bool() const { return val; }
  void set(bool v);

  void printUsage(int colwidth) const override;
  void parse(const std::string& v) override;
};

template <typename T>
class ValOption : public Option {
  T val;
  std::string checkDescription;
  std::function<bool(const T&)> check;

 public:
  ValOption(const std::string& n, const std::string& d, const T& v, const std::string& cd,
            const std::function<bool(const T&)>& c)
      : Option{n, d}, val(v), checkDescription(cd), check(c) {}

  const T& get() const { return val; }
  void set(const T& v) { val = v; }

  void printUsage(int colwidth) const override {
    std::stringstream output;
    output << " --" << name << "=" << val << " ";
    std::cout << output.str();
    for (int i = 0; i < colwidth - (int)output.str().size(); ++i) std::cout << " ";
    std::cout << description << " (" << checkDescription << ")\n";
  }

  void parse(const std::string& v) override {
    try {
      set(aux::sto<T>(v));
    } catch (const std::invalid_argument& ia) {
      throw InvalidArgument("Invalid value for " + name + ": " + v + ".\nCheck usage with --help option.");
    }
    if (!check(val)) {
      throw InvalidArgument("Invalid value for " + name + ": " + v + ".\nCheck usage with --help option.");
    }
  }
};

class EnumOption : public Option {
  std::string val;
  std::vector<std::string> values;

 public:
  EnumOption(const std::string& n, const std::string& d, const std::string& v, const std::vector<std::string>& vs);

  void printUsage(int colwidth) const override;

  [[nodiscard]] bool valid(const std::string& v) const;

  void parse(const std::string& v) override;

  [[nodiscard]] bool is(const std::string& v) const;
  [[nodiscard]] const std::string& get() const;
};

struct Options {
  VoidOption help{"help", "Print this help message"};
  VoidOption copyright{"copyright", "Print copyright information"};
  EnumOption licenseInfo{"license",
                         "Print the license text of the given license",
                         "",
                         {
                             "AGPLv3",
                             "Boost",
#if WITHCOINUTILS
                             "EPL",
#endif
                             "MIT",
                             "RS",
#if WITHSOPLEX
                             "ZIB",
#endif
                         }};
  ValOption<long long> randomSeed{"seed", "Seed for the pseudo-random number generator", 1, "1 =< int",
                                  [](long long x) -> bool { return 1 <= x; }};
  VoidOption noSolve{"onlyparse", "Quit after parsing file"};
  EnumOption fileFormat{
      "format", "File format (overridden by corresponding file extension)", "opb", {"opb", "cnf", "wcnf", "mps", "lp"}};
  BoolOption uniformOut{"out-uniform", "Use the default opb output style even for other file formats", false};
  VoidOption printOpb{"print-opb", "Print OPB of the parsed problem"};
  VoidOption printSol{"print-sol", "Print the solution if found"};
  VoidOption printUnits{"print-units", "Print unit literals"};
  VoidOption printCsvData{"print-csv", "Print statistics in a comma-separated value format"};
  ValOption<int> verbosity{"verbosity", "Verbosity of the output", 0, "0 =< int",
                           [](const int& x) -> bool { return x >= 0; }};
  ValOption<std::string> proofLog{"proof-log", "Filename for the proof logs, left unspecified disables proof logging",
                                  "", "/path/to/file", [](const std::string&) -> bool { return true; }};
  BoolOption proofZip{"proof-zip", "Generate proof file in ZIP format. This can alleviate space and IO constraints.",
                      false};
  ValOption<double> timeout{"timeout", "Timeout in seconds, 0 is infinite ", 0, "0 =< float",
                            [](double x) -> bool { return 0 <= x; }};
  ValOption<long long> timeoutDet{"timeout-det", "Deterministic timeout, 0 is infinite ", 0, "0 =< int",
                                  [](long long x) -> bool { return 0 <= x; }};
  ValOption<double> lubyBase{"luby-base", "Base of the Luby restart sequence", 2, "1 =< float",
                             [](double x) -> bool { return 1 <= x; }};
  ValOption<int> lubyMult{"luby-mult", "Multiplier of the Luby restart sequence", 100, "1 =< int",
                          [](const int& x) -> bool { return x >= 1; }};
  ValOption<double> varWeight{
      "var-weight", "Activity weight for latest conflict variables - 0 = fixed activity, 0.5 = ACIDS, 1 = VMTF.", 0.99,
      "0 =< float =< 1", [](const double& x) -> bool { return 0 <= x && x <= 1; }};
  BoolOption varSeparate{"var-separate", "Use separate phase and activity for linear and core-guided phases", true};
  ValOption<int> dbDecayLBD{"db-decay", "Decay term for the LBD of constraints", 1, "0 (no decay) =< int",
                            [](const int& x) -> bool { return 0 <= x; }};
  ValOption<double> dbExp{"db-exp",
                          "Exponent of the growth of the learned constraint database and the inprocessing intervals, "
                          "with log(#conflicts) as base",
                          1.1, "0 =< float", [](const double& x) -> bool { return 0 <= x; }};
  ValOption<double> dbScale{"db-scale", "Multiplier of the learned clause database and inprocessing intervals", 500,
                            "0 < float", [](const double& x) -> bool { return 0 < x; }};
  ValOption<int> dbSafeLBD{"db-safelbd", "Learned constraints with this LBD or less are safe from database cleanup", 1,
                           "0 (nobody is safe) =< int", [](const int& x) -> bool { return 0 <= x; }};
  ValOption<double> propWatched{"prop-watched", "Watched propagation instead of counting propagation", 1,
                                "0 (always counting) =< float =< 1 (always watched)",
                                [](const double& x) -> bool { return 0 <= x && x <= 1e9; }};
  ValOption<double> lpTimeRatio {
    "lp", "Ratio of time spent in LP calls (0 means no LP solving, 1 means no limit on LP solver)",
#if WITHSOPLEX
        0.1, "0 =< float <= 1", [](const double& x) -> bool { return 1 >= x && x >= 0; }
#else
        0, "0", [](const double& x) -> bool { return x == 0; }
#endif
  };
  ValOption<int> lpPivotBudget{"lp-budget", "Initial LP call pivot budget", 2000, "1 =< int",
                               [](const int& x) -> bool { return x >= 1; }};
  ValOption<double> lpIntolerance{"lp-intolerance", "Intolerance for floating point artifacts", 1e-6, "0 < float",
                                  [](const double& x) -> bool { return x > 1; }};
  BoolOption lpLearnDuals{"lp-learnduals", "Learn dual constraints from optimal LP", true};
  BoolOption lpGomoryCuts{"lp-cut-gomory", "Generate Gomory cuts", false};
  BoolOption lpLearnedCuts{"lp-cut-learned", "Use learned constraints as cuts", false};
  ValOption<int> lpGomoryCutLimit{"lp-cut-gomlim",
                                  "Max number of tableau rows considered for Gomory cuts in a single round", 100,
                                  "1 =< int", [](const int& x) -> bool { return 1 <= x; }};
  ValOption<double> lpMaxCutCos{
      "lp-cut-maxcos",
      "Upper bound on cosine of angle between cuts added in one round, higher means cuts can be more parallel", 0.1,
      "0 =< float =< 1", [](const double& x) -> bool { return 0 <= x && x <= 1; }};
  BoolOption multBeforeDiv{"ca-multiply", "Multiply reason with the asserting literal's conflict coefficient", true};
  EnumOption division{"ca-division",
                      "Division method to round the reason to non-positive slack",
                      "mindiv",
                      {"rto", "slack+1", "mindiv"}};
  BoolOption weakenNonImplying{"ca-weaken-nonimplying",
                               "Weaken non-implying falsified literals from learned constraints", true};
  BoolOption learnedMin{"ca-min", "Minimize learned constraints through generalized self-subsumption.", true};
  BoolOption caCancelingUnkns{"ca-cancelingunknowns", "Exploit canceling unknowns", true};
  ValOption<int> bitsOverflow{"bits-overflow",
                              "Bit width of maximum coefficient during conflict analysis calculations (0 is unlimited, "
                              "unlimited or greater than 62 may use slower arbitrary precision implementations)",
                              limitBitConfl<int128, int128>(), "0 =< int", [](const int& x) -> bool { return x >= 0; }};
  ValOption<int> bitsReduced{"bits-reduced",
                             "Bit width of maximum coefficient after reduction when exceeding bits-overflow (0 is "
                             "unlimited, 1 reduces to cardinalities)",
                             limitBit<int, long long>(), "0 =< int", [](const int& x) -> bool { return x >= 0; }};
  ValOption<int> bitsLearned{
      "bits-learned",
      "Bit width of maximum coefficient for learned constraints (0 is unlimited, 1 reduces to cardinalities)",
      limitBit<int, long long>(), "0 =< int", [](const int& x) -> bool { return x >= 0; }};
  EnumOption optMethod{
      "opt-method", "Optimization method", "mixed", {"topdown", "bottomup", "mixed", "ranged", "random", "bisect"}};
  ValOption<int32_t> objRange{
      "opt-objrange",
      "Range of objective reformulation, higher means more finegrained search over objective (0 disables)", 50,
      "0 or int > 1", [](const int32_t& x) -> bool { return x == 0 || x > 1; }};
  ValOption<float> cgHybrid{"cg",
                            "Ratio of core-guided optimization time (0 means no core-guided, 1 fully core-guided)", 0.5,
                            "0 =< float =< 1", [](const double& x) -> bool { return x >= 0 && x <= 1; }};
  BoolOption cgResolveProp{"cg-resprop", "Resolve propagated assumptions when extracting cores", true};
  ValOption<float> cgStrat{"cg-strat", "Stratification factor (1 disables stratification, higher means greater strata)",
                           2, "1 =< float", [](const float& x) -> bool { return x >= 1; }};
  EnumOption ilpEncoding{"ilp-encoding", "Encoding of integer variables", "log", {"log", "order", "onehot"}};
  BoolOption ilpContinuous{"ilp-continuous",
                           "Accept continuous variables by treating them as integer variables. This restricts the "
                           "problem and may yield UNSAT when no integer solution exists.",
                           false};
  BoolOption ilpUnbounded{"ilp-unbounded",
                          "Accept unbounded integer variables by imposing default bounds. This restricts the problem "
                          "and may yield UNSAT when no solution within the bounds exists.",
                          true};
  ValOption<double> ilpDefaultBound{"ilp-defbound", "Default bound used for unbounded integer variables",
                                    limitAbs<int, long long>(), "0 < double",
                                    [](const double& x) -> bool { return x > 0; }};
  BoolOption pureLits{"inp-purelits", "Propagate pure literals", false};
  ValOption<long long> domBreakLim{
      "inp-dombreaklim",
      "Maximum limit of queried constraints for dominance breaking (0 means no dominance breaking, -1 is unlimited)", 0,
      "-1 =< int", [](const int& x) -> bool { return x >= -1; }};
  BoolOption inpProbing{"inp-probing", "Perform probing", true};
  ValOption<double> inpAMO{"inp-atmostone",
                           "Ratio of time spent detecting at-most-ones (0 means none, 1 means unlimited)", 0.1,
                           "0 =< float <= 1", [](const double& x) -> bool { return 1 >= x && x >= 0; }};
  ValOption<DetTime> basetime{"inp-basetime", "Initial deterministic time allotted to presolve techniques", 1,
                              "0 =< float", [](const DetTime& x) -> bool { return x >= 0; }};

  const std::vector<Option*> options = {
      &help,
      &copyright,
      &licenseInfo,
      &randomSeed,
      &noSolve,
      &fileFormat,
      &uniformOut,
      &printOpb,
      &printSol,
      &printUnits,
      &printCsvData,
      &verbosity,
      &timeout,
      &timeoutDet,
      &proofLog,
      &proofZip,
      &lubyBase,
      &lubyMult,
      &varWeight,
      &varSeparate,
      &dbDecayLBD,
      &dbExp,
      &dbScale,
      &dbSafeLBD,
      &propWatched,
#if WITHSOPLEX
      &lpTimeRatio,
      &lpPivotBudget,
      &lpIntolerance,
      &lpLearnDuals,
      &lpGomoryCuts,
      &lpLearnedCuts,
      &lpGomoryCutLimit,
      &lpMaxCutCos,
#endif  // WITHSOPLEX
      &multBeforeDiv,
      &division,
      &weakenNonImplying,
      &learnedMin,
      &caCancelingUnkns,
      &bitsOverflow,
      &bitsReduced,
      &bitsLearned,
      &optMethod,
      &objRange,
      &cgHybrid,
      &cgResolveProp,
      &cgStrat,
      &ilpEncoding,
      &ilpContinuous,
      &ilpUnbounded,
      &ilpDefaultBound,
      &pureLits,
      &domBreakLim,
      &inpProbing,
      &inpAMO,
      &basetime,
  };
  unordered_map<std::string, Option*> name2opt;

  std::string formulaName;

  Options();

  void parseOption(const std::string& option, const std::string& value);
  void parseCommandLine(int argc, char** argv);
  void usage(const char* name);
};

}  // namespace xct
