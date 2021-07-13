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

#include "aux.hpp"
#include "globals.hpp"
#include "quit.hpp"
#include "used_licenses/licenses.hpp"

namespace rs {

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
  VoidOption(const std::string& n, const std::string& d) : Option{n, d} {}

  explicit operator bool() const { return val; }

  void printUsage(int colwidth) const override {
    std::cout << " --" << name;
    for (int i = name.size() + 3; i < colwidth; ++i) std::cout << " ";
    std::cout << description << "\n";
  }

  void parse([[maybe_unused]] const std::string& v) override {
    assert(v.empty());
    val = true;
  }
};

class BoolOption : public Option {
  bool val = false;

 public:
  BoolOption(const std::string& n, const std::string& d, bool v) : Option{n, d}, val(v) {}

  explicit operator bool() const { return val; }

  void printUsage(int colwidth) const override {
    std::stringstream output;
    output << " --" << name << "=" << val << " ";
    std::cout << output.str();
    for (int i = 0; i < colwidth - (int)output.str().size(); ++i) std::cout << " ";
    std::cout << description << " (0 or 1)\n";
  }

  void parse(const std::string& v) override {
    try {
      val = std::stoi(v);
    } catch (const std::invalid_argument& ia) {
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    }
    if (val != 0 && val != 1)
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
  }
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

  void printUsage(int colwidth) const override {
    std::stringstream output;
    output << " --" << name << "=" << val << " ";
    std::cout << output.str();
    for (int i = 0; i < colwidth - (int)output.str().size(); ++i) std::cout << " ";
    std::cout << description << " (" << checkDescription << ")\n";
  }

  void parse(const std::string& v) override {
    try {
      val = aux::sto<T>(v);
    } catch (const std::invalid_argument& ia) {
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    }
    if (!check(val)) quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
  }
};

class EnumOption : public Option {
  std::string val;
  std::vector<std::string> values;

 public:
  EnumOption(const std::string& n, const std::string& d, const std::string& v, const std::vector<std::string>& vs)
      : Option{n, d}, val(v), values(vs) {}

  void printUsage(int colwidth) const override {
    std::stringstream output;
    output << " --" << name << "=" << val << " ";
    std::cout << output.str();
    for (int i = 0; i < colwidth - (int)output.str().size(); ++i) std::cout << " ";
    std::cout << description << " (";
    for (int i = 0; i < (int)values.size(); ++i) {
      if (i > 0) std::cout << ", ";
      std::cout << values[i];
    }
    std::cout << ")\n";
  }

  [[nodiscard]] bool valid(const std::string& v) const {
    return std::find(std::begin(values), std::end(values), v) != std::end(values);
  }

  void parse(const std::string& v) override {
    if (!valid(v)) quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    val = v;
  }

  [[nodiscard]] bool is(const std::string& v) const {
    assert(valid(v));
    return val == v;
  }

  [[nodiscard]] const std::string& get() const { return val; }
};

struct Options {
  VoidOption help{"help", "Print this help message"};
  VoidOption copyright{"copyright", "Print copyright information"};
  EnumOption licenseInfo{"license",
                         "Print the license text of the given license",
                         "",
                         {
                             "MIT",
                             "RS",
                             "Boost",
#ifdef WITHSOPLEX
                             "ZIB",
#endif
#ifdef WITHCOINUTILS
                             "EPL",
#endif
                         }};
  ValOption<long long> randomSeed{"seed", "Seed for the pseudo-random number generator", 1, "1 =< int",
                                  [](long long x) -> bool { return 1 <= x; }};
  VoidOption noSolve{"onlyparse", "Quit after parsing file"};
  EnumOption fileFormat{
      "format", "File format (overridden by corresponding file extension)", "opb", {"opb", "cnf", "wcnf", "mps", "lp"}};
  VoidOption printOpb{"print-opb", "Print OPB of the parsed problem"};
  VoidOption printSol{"print-sol", "Print the solution if found"};
  VoidOption printUnits{"print-units", "Print unit literals"};
  VoidOption printCsvData{"print-csv", "Print statistics in a comma-separated value format"};
  EnumOption outputMode{"output",
                        "Output format to be adhered to (for competitions)",
                        "default",
                        {"default", "maxsat", "maxsatnew", "miplib"}};
  ValOption<int> verbosity{"verbosity", "Verbosity of the output", 1, "0 =< int",
                           [](const int& x) -> bool { return x >= 0; }};
  ValOption<std::string> proofLog{"proof-log", "Filename for the proof logs, left unspecified disables proof logging",
                                  "", "/path/to/file", [](const std::string&) -> bool { return true; }};
  ValOption<double> timeout{"timeout", "Timeout in seconds, 0 is infinite ", 0, "0 =< float",
                            [](double x) -> bool { return 0 <= x; }};
  ValOption<long long> timeoutDet{"timeout-det", "Deterministic timeout, 0 is infinite ", 0, "0 =< int",
                                  [](long long x) -> bool { return 0 <= x; }};
  ValOption<int> enumerate{"enumerate",
                           "For a decision problem, keep enumerating solutions until this number are found.", 1,
                           "0 (no limit) =< int", [](const int& x) -> bool { return x >= 0; }};
  ValOption<double> lubyBase{"luby-base", "Base of the Luby restart sequence", 2, "1 =< float",
                             [](double x) -> bool { return 1 <= x; }};
  ValOption<int> lubyMult{"luby-mult", "Multiplier of the Luby restart sequence", 100, "1 =< int",
                          [](const int& x) -> bool { return x >= 1; }};
  ValOption<double> varDecay{"var-decay", "Variable heuristic VSIDS decay", 0.9, "0.5 =< float < 1",
                             [](const double& x) -> bool { return 0.5 <= x && x < 1; }};
  BoolOption varOrder{"var-order", "Use fixed variable order instead of VSIDS", false};
  BoolOption varSeparate{"var-separate", "Use separate phase and activity for linear and core-guided phases", true};
  BoolOption varInitAct{"var-init", "Initialize activity based on watches and initial local search call", false};
  ValOption<int> dbDecayLBD{"db-decay", "Decay term for the LBD of constraints", 1, "0 (no decay) =< int",
                            [](const int& x) -> bool { return 0 <= x; }};
  ValOption<double> dbExp{"db-exp",
                          "Exponent of the growth of the learned clause database and the inprocessing intervals, "
                          "with log(#conflicts) as base",
                          3.5, "0 =< float", [](const double& x) -> bool { return 0 <= x; }};
  ValOption<int> dbSafeLBD{"db-safelbd", "Learned constraints with this LBD or less are safe from database cleanup", 1,
                           "0 (nobody is safe) =< int", [](const int& x) -> bool { return 0 <= x; }};
  ValOption<double> propCounting{"prop-counting", "Counting propagation instead of watched propagation", 0.6,
                                 "0 (no counting) =< float =< 1 (always counting)",
                                 [](const double& x) -> bool { return 0 <= x && x <= 1; }};
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
  BoolOption slackdiv{"ca-slackdiv",
                      "Use slack+1 as divisor for reason constraints (instead of the asserting coefficient)", false};
  BoolOption weakenNonImplying{"ca-weaken-nonimplying",
                               "Weaken non-implying falsified literals from learned constraints", true};
  BoolOption learnedMin{"ca-min", "Minimize learned constraints through generalized self-subsumption.", true};
  BoolOption bumpOnlyFalse{"bump-onlyfalse",
                           "Bump activity of literals encountered during conflict analysis only when falsified", false};
  BoolOption bumpCanceling{"bump-canceling",
                           "Bump activity of literals encountered during conflict analysis when canceling", false};
  BoolOption bumpLits{
      "bump-lits",
      "Bump activity of literals encountered during conflict analysis, twice when occurring with opposing sign", false};
  ValOption<int> bitsOverflow{"bits-overflow",
                              "Bit width of maximum coefficient during conflict analysis calculations (0 is unlimited, "
                              "unlimited or greater than 62 may use slower arbitrary precision implementations)",
                              conflLimit64, "0 =< int", [](const int& x) -> bool { return x >= 0; }};
  ValOption<int> bitsReduced{"bits-reduced",
                             "Bit width of maximum coefficient after reduction when exceeding bits-overflow (0 is "
                             "unlimited, 1 reduces to cardinalities)",
                             conflLimit64 - 10, "0 =< int", [](const int& x) -> bool { return x >= 0; }};
  ValOption<int> bitsLearned{
      "bits-learned",
      "Bit width of maximum coefficient for learned constraints (0 is unlimited, 1 reduces to cardinalities)",
      limit32bit, "0 =< int", [](const int& x) -> bool { return x >= 0; }};
  ValOption<float> cgHybrid{"cg",
                            "Ratio of core-guided optimization time (0 means no core-guided, 1 fully core-guided)", 0.5,
                            "0 =< float =< 1", [](const double& x) -> bool { return x >= 0 && x <= 1; }};
  EnumOption cgEncoding{
      "cg-encoding", "Encoding of the extension constraints", "lazysum", {"sum", "lazysum", "reified"}};
  BoolOption cgResolveProp{"cg-resprop", "Resolve propagated assumptions when extracting cores", true};
  ValOption<float> cgStrat{"cg-strat", "Stratification factor (1 disables stratification, higher means greater strata)",
                           2, "1 =< float", [](const float& x) -> bool { return x >= 1; }};
  ValOption<int> intEncoding{
      "int-orderenc",
      "Upper bound on the range size of order-encoded integer variables, any larger will be encoded binary-wise", 12,
      "2 =< int", [](const int& x) -> bool { return x >= 2; }};
  ValOption<double> intDefaultBound{"int-infinity", "Bound used for unbounded integer variables", limit32, "0 < double",
                                    [](const double& x) -> bool { return x > 0; }};
  BoolOption pureLits{"inp-purelits", "Propagate pure literals", true};
  ValOption<long long> domBreakLim{
      "inp-dombreaklim",
      "Maximum limit of queried constraints for dominance breaking (0 means no dominance breaking, -1 is unlimited)",
      -1, "-1 =< int", [](const int& x) -> bool { return x >= -1; }};
  ValOption<double> tabuLim{"inp-localsearch", "Ratio of time spent on local search (0 means none, 1 means unlimited)",
                            0.00, "0 =< float <= 1", [](const double& x) -> bool { return 1 >= x && x >= 0; }};
  BoolOption inpProbing{"inp-probing", "Perform probing", true};
  ValOption<double> inpAMO{"inp-atmostone",
                           "Ratio of time spent detecting at-most-ones (0 means none, 1 means unlimited)", 0.1,
                           "0 =< float <= 1", [](const double& x) -> bool { return 1 >= x && x >= 0; }};
  ValOption<long double> basetime{"inp-basetime", "Initial deterministic time allotted to presolve techniques", 1e8,
                                  "0=< float", [](const long double& x) -> bool { return x >= 0; }};

  BoolOption test{"test", "Activate change under review", false};

  const std::vector<Option*> options = {
      &help,
      &copyright,
      &licenseInfo,
      &randomSeed,
      &noSolve,
      &fileFormat,
      &printOpb,
      &printSol,
      &printUnits,
      &printCsvData,
      &outputMode,
      &verbosity,
      &timeout,
      &timeoutDet,
      &proofLog,
      &enumerate,
      &lubyBase,
      &lubyMult,
      &varDecay,
      &varOrder,
      &varSeparate,
      &varInitAct,
      &dbDecayLBD,
      &dbExp,
      &dbSafeLBD,
      &propCounting,
      &lpTimeRatio,
      &lpPivotBudget,
      &lpIntolerance,
      &lpLearnDuals,
      &lpGomoryCuts,
      &lpLearnedCuts,
      &lpGomoryCutLimit,
      &lpMaxCutCos,
      &slackdiv,
      &weakenNonImplying,
      &learnedMin,
      &bumpOnlyFalse,
      &bumpCanceling,
      &bumpLits,
      &bitsOverflow,
      &bitsReduced,
      &bitsLearned,
      &cgHybrid,
      &cgEncoding,
      &cgResolveProp,
      &cgStrat,
      &intEncoding,
      &intDefaultBound,
      &pureLits,
      &domBreakLim,
      &tabuLim,
      &inpProbing,
      &inpAMO,
      &basetime,
      &test,
  };
  std::unordered_map<std::string, Option*> name2opt;

  Options() {
    for (Option* opt : options) name2opt[opt->name] = opt;
  }

  std::string formulaName;

  void parseCommandLine(int argc, char** argv) {
    std::unordered_map<std::string, std::string> opt_val;
    for (int i = 1; i < argc; i++) {
      std::string arg = argv[i];
      if (arg.substr(0, 2) != "--") {
        formulaName = arg;
      } else {
        size_t eqindex = std::min(arg.size(), arg.find('='));
        std::string inputopt = arg.substr(2, eqindex - 2);
        if (name2opt.count(inputopt) == 0) {
          quit::exit_ERROR({"Unknown option: ", inputopt, ".\nCheck usage with ", argv[0], " --help"});
        } else {
          name2opt[inputopt]->parse(arg.substr(std::min(arg.size(), eqindex + 1)));
        }
      }
    }

    if (help) {
      usage(argv[0]);
      rs::aux::flushexit(0);
    } else if (copyright) {
      licenses::printUsed();
      rs::aux::flushexit(0);
    } else if (licenseInfo.get() != "") {
      licenses::printLicense(licenseInfo.get());
      rs::aux::flushexit(0);
    }
  }

  void usage(const char* name) {
    std::cout << "Usage: " << name << " [OPTIONS] instancefile\n";
    std::cout << "or     cat instancefile | " << name << " [OPTIONS]\n";
    std::cout << "Options:\n";
    for (Option* opt : options) opt->printUsage(24);
  }

  bool enumerateSolutions() const { return enumerate.get() != 1; }
};

}  // namespace rs
