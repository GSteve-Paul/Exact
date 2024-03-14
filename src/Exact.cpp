/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2024 Jo Devriendt, Nonfiction Software

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

#include "Exact.hpp"
#include <csignal>
#include <fstream>
#include "parsing.hpp"

using namespace xct;

IntVar* Exact::getVariable(const std::string& name) const {
  IntVar* res = ilp.getVarFor(name);
  if (!res) throw InvalidArgument("No variable " + name + " found.");
  return res;
}

std::vector<IntVar*> Exact::getVars(const std::vector<std::string>& names) const {
  return aux::comprehension(names, [&](const std::string& name) { return getVariable(name); });
}

// TODO: reduce below code duplication using templates?

bigint getCoef(int64_t c) { return static_cast<bigint>(c); }
bigint getCoef(const std::string& c) { return bigint(c); }

std::vector<bigint> getCoefs(const std::vector<int64_t>& cs) {
  return aux::comprehension(cs, [](int64_t x) { return getCoef(x); });
}
std::vector<bigint> getCoefs(const std::vector<std::string>& cs) {
  return aux::comprehension(cs, [](const std::string& x) { return getCoef(x); });
}

Options getOptions(const std::vector<std::pair<std::string, std::string>>& options) {
  Options opts;
  for (auto pr : options) {
    opts.parseOption(pr.first, pr.second);
  }
  return opts;
}

Exact::Exact(const std::vector<std::pair<std::string, std::string>>& options) : ilp(getOptions(options), true) {
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif
}

void Exact::addVariable(const std::string& name, int64_t lb, int64_t ub, const std::string& encoding) {
  if (ilp.getVarFor(name)) throw InvalidArgument("Variable " + name + " already exists.");
  if (encoding != "" && encoding != "order" && encoding != "log" && encoding != "onehot") {
    throw InvalidArgument("Unknown encoding " + encoding +
                          ". Should be \"log\", \"order\" or \"onehot\", or left unspecified.");
  }
  ilp.addVar(name, getCoef(lb), getCoef(ub), opt2enc(encoding == "" ? ilp.global.options.ilpEncoding.get() : encoding));
}

void Exact::addVariable(const std::string& name, const std::string& lb, const std::string& ub,
                        const std::string& encoding) {
  if (ilp.getVarFor(name)) throw InvalidArgument("Variable " + name + " already exists.");
  if (encoding != "" && encoding != "order" && encoding != "log" && encoding != "onehot") {
    throw InvalidArgument("Unknown encoding " + encoding +
                          ". Should be \"log\", \"order\" or \"onehot\", or left unspecified.");
  }
  ilp.addVar(name, getCoef(lb), getCoef(ub), opt2enc(encoding == "" ? ilp.global.options.ilpEncoding.get() : encoding));
}

std::vector<std::string> Exact::getVariables() const {
  return aux::comprehension(ilp.getVariables(), [](IntVar* iv) { return iv->getName(); });
}

void Exact::addConstraint(const std::vector<std::pair<int64_t, std::string>>& terms, bool useLB, int64_t lb, bool useUB,
                          int64_t ub) {
  if (terms.size() > 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, aux::option(useLB, getCoef(lb)), aux::option(useUB, getCoef(ub))};
  ic.lhs.resize(terms.size());
  for (const auto& t : terms) {
    ic.lhs.push_back({getCoef(t.first), getVariable(t.second)});
  }
  ilp.addConstraint(ic);
}
void Exact::addConstraint(const std::vector<std::pair<std::string, std::string>>& terms, bool useLB,
                          const std::string& lb, bool useUB, const std::string& ub) {
  if (terms.size() > 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, aux::option(useLB, getCoef(lb)), aux::option(useUB, getCoef(ub))};
  ic.lhs.reserve(terms.size());
  for (const auto& t : terms) {
    ic.lhs.push_back({getCoef(t.first), getVariable(t.second)});
  }
  ilp.addConstraint(ic);
}

void Exact::addReification(const std::string& head, bool sign, const std::vector<int64_t>& coefs,
                           const std::vector<std::string>& vars, int64_t lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.resize(coefs.size());
  for (int64_t i = 0; i < (int64_t)coefs.size(); ++i) {
    ic.lhs[i] = {getCoef(coefs[i]), getVariable(vars[i])};
  }
  ilp.addReification(getVariable(head), sign, ic);
}
void Exact::addReification(const std::string& head, bool sign, const std::vector<std::string>& coefs,
                           const std::vector<std::string>& vars, const std::string& lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.resize(coefs.size());
  for (int64_t i = 0; i < (int64_t)coefs.size(); ++i) {
    ic.lhs[i] = {getCoef(coefs[i]), getVariable(vars[i])};
  }
  ilp.addReification(getVariable(head), sign, ic);
}
void Exact::addRightReification(const std::string& head, bool sign, const std::vector<int64_t>& coefs,
                                const std::vector<std::string>& vars, int64_t lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.resize(coefs.size());
  for (int64_t i = 0; i < (int64_t)coefs.size(); ++i) {
    ic.lhs[i] = {getCoef(coefs[i]), getVariable(vars[i])};
  }
  ilp.addRightReification(getVariable(head), sign, ic);
}
void Exact::addRightReification(const std::string& head, bool sign, const std::vector<std::string>& coefs,
                                const std::vector<std::string>& vars, const std::string& lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.resize(coefs.size());
  for (int64_t i = 0; i < (int64_t)coefs.size(); ++i) {
    ic.lhs[i] = {getCoef(coefs[i]), getVariable(vars[i])};
  }
  ilp.addRightReification(getVariable(head), sign, ic);
}
void Exact::addLeftReification(const std::string& head, bool sign, const std::vector<int64_t>& coefs,
                               const std::vector<std::string>& vars, int64_t lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.resize(coefs.size());
  for (int64_t i = 0; i < (int64_t)coefs.size(); ++i) {
    ic.lhs[i] = {getCoef(coefs[i]), getVariable(vars[i])};
  }
  ilp.addLeftReification(getVariable(head), sign, ic);
}
void Exact::addLeftReification(const std::string& head, bool sign, const std::vector<std::string>& coefs,
                               const std::vector<std::string>& vars, const std::string& lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.resize(coefs.size());
  for (int64_t i = 0; i < (int64_t)coefs.size(); ++i) {
    ic.lhs[i] = {getCoef(coefs[i]), getVariable(vars[i])};
  }
  ilp.addLeftReification(getVariable(head), sign, ic);
}

void Exact::fix(const std::string& var, int64_t val) { ilp.fix(getVariable(var), getCoef(val)); }
void Exact::fix(const std::string& var, const std::string& val) { ilp.fix(getVariable(var), getCoef(val)); }

void Exact::setAssumption(const std::string& var, const std::vector<int64_t>& vals) {
  ilp.setAssumption(getVariable(var), getCoefs(vals));
}
void Exact::setAssumption(const std::string& var, const std::vector<std::string>& vals) {
  ilp.setAssumption(getVariable(var), getCoefs(vals));
}

void Exact::clearAssumptions() { ilp.clearAssumptions(); }
void Exact::clearAssumption(const std::string& var) { ilp.clearAssumption(getVariable(var)); }

bool Exact::hasAssumption(const std::string& var) const { return ilp.hasAssumption(getVariable(var)); }
std::vector<int64_t> Exact::getAssumption(const std::string& var) const {
  return aux::comprehension(ilp.getAssumption(getVariable(var)),
                            [](const bigint& i) { return static_cast<int64_t>(i); });
}
std::vector<std::string> Exact::getAssumption_arb(const std::string& var) const {
  return aux::comprehension(ilp.getAssumption(getVariable(var)), [](const bigint& i) { return aux::str(i); });
}

void Exact::setSolutionHints(const std::vector<std::string>& vars, const std::vector<int64_t>& vals) {
  ilp.setSolutionHints(getVars(vars), getCoefs(vals));
}
void Exact::setSolutionHints(const std::vector<std::string>& vars, const std::vector<std::string>& vals) {
  ilp.setSolutionHints(getVars(vars), getCoefs(vals));
}

void Exact::clearSolutionHints(const std::vector<std::string>& vars) { ilp.clearSolutionHints(getVars(vars)); }

void Exact::boundObjByLastSol() { ilp.getOptim()->boundObjByLastSol(); }
void Exact::invalidateLastSol() { ilp.invalidateLastSol(); }
void Exact::invalidateLastSol(const std::vector<std::string>& vars) { ilp.invalidateLastSol(getVars(vars)); }

void Exact::printVariables() const { ilp.printVars(std::cout); }
void Exact::printInput() const { ilp.printInput(std::cout); }
void Exact::printFormula() { ilp.printFormula(std::cout); }

void Exact::setObjective(const std::vector<std::pair<int64_t, std::string>>& terms, bool minimize, int64_t offset) {
  if (terms.size() > 1e9) throw InvalidArgument("Objective has more than 1e9 terms.");

  std::vector<IntTerm> iterms;
  iterms.reserve(terms.size());
  for (const auto& t : terms) {
    iterms.push_back({getCoef(t.first), getVariable(t.second)});
  }
  ilp.setObjective(iterms, minimize, offset);
}

void Exact::setObjective(const std::vector<std::pair<std::string, std::string>>& terms, bool minimize,
                         const std::string& offset) {
  if (terms.size() > 1e9) throw InvalidArgument("Objective has more than 1e9 terms.");

  std::vector<IntTerm> iterms;
  iterms.reserve(terms.size());
  for (const auto& t : terms) {
    iterms.push_back({getCoef(t.first), getVariable(t.second)});
  }
  ilp.setObjective(iterms, minimize, getCoef(offset));
}

SolveState Exact::runOnce(double timeout) {
  if (timeout != 0) ilp.global.stats.runStartTime = std::chrono::steady_clock::now();
  return ilp.getOptim()->run(false, timeout);
}

SolveState Exact::runFull(bool optimize, double timeout) {
  if (timeout != 0) ilp.global.stats.runStartTime = std::chrono::steady_clock::now();
  ilp.getSolver().printHeader();
  return ilp.getOptim()->runFull(optimize, timeout);
}

std::pair<int64_t, int64_t> Exact::getObjectiveBounds() const {
  return {static_cast<int64_t>(ilp.getLowerBound()), static_cast<int64_t>(ilp.getUpperBound())};
}
std::pair<std::string, std::string> Exact::getObjectiveBounds_arb() const {
  return {aux::str(ilp.getLowerBound()), aux::str(ilp.getUpperBound())};
}

bool Exact::hasSolution() const { return ilp.getSolver().foundSolution(); }

std::vector<int64_t> Exact::getLastSolutionFor(const std::vector<std::string>& vars) const {
  if (!hasSolution()) throw InvalidArgument("No solution can be returned if no solution has been found.");
  return aux::comprehension(ilp.getLastSolutionFor(getVars(vars)),
                            [](const bigint& i) { return static_cast<int64_t>(i); });
}
std::vector<std::string> Exact::getLastSolutionFor_arb(const std::vector<std::string>& vars) const {
  return aux::comprehension(ilp.getLastSolutionFor(getVars(vars)), [](const bigint& i) { return aux::str(i); });
}

std::vector<std::string> Exact::getLastCore() {
  Core core = ilp.getLastCore();
  if (core) {
    return aux::comprehension(*core, [](IntVar* iv) { return iv->getName(); });
  } else {
    return {};
  }
}

void Exact::printStats() { quit::printFinalStats(ilp); }

std::vector<std::pair<int64_t, int64_t>> Exact::propagate(const std::vector<std::string>& vars, double timeout) {
  return aux::comprehension(
      ilp.propagate(getVars(vars), true, {true, timeout}), [](const std::pair<bigint, bigint>& x) {
        return std::pair<int64_t, int64_t>(static_cast<int64_t>(x.first), static_cast<int64_t>(x.second));
      });
}
std::vector<std::pair<std::string, std::string>> Exact::propagate_arb(const std::vector<std::string>& vars,
                                                                      double timeout) {
  return aux::comprehension(ilp.propagate(getVars(vars), true, {true, timeout}),
                            [](const std::pair<bigint, bigint>& x) {
                              return std::pair<std::string, std::string>(aux::str(x.first), aux::str(x.second));
                            });
}

std::vector<std::vector<int64_t>> Exact::pruneDomains(const std::vector<std::string>& vars, double timeout) {
  return aux::comprehension(ilp.pruneDomains(getVars(vars), true, {true, timeout}), [](const std::vector<bigint>& x) {
    return aux::comprehension(x, [](const bigint& y) { return static_cast<int64_t>(y); });
  });
}
std::vector<std::vector<std::string>> Exact::pruneDomains_arb(const std::vector<std::string>& vars, double timeout) {
  return aux::comprehension(ilp.pruneDomains(getVars(vars), true, {true, timeout}), [](const std::vector<bigint>& x) {
    return aux::comprehension(x, [](const bigint& y) { return aux::str(y); });
  });
}

int64_t Exact::count(const std::vector<std::string>& vars, double timeout) {
  return ilp.count(getVars(vars), true, {true, timeout}).second;
}
