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

std::vector<IntVar*> Exact::getVariables(const std::vector<std::string>& names) const {
  return aux::comprehension(names, [&](const std::string& name) { return getVariable(name); });
}

// TODO: reduce below code duplication using templates?

bigint getCoef(long long c) { return static_cast<bigint>(c); }
bigint getCoef(const std::string& c) { return bigint(c); }

std::vector<bigint> getCoefs(const std::vector<long long>& cs) {
  return aux::comprehension(cs, [](long long x) { return getCoef(x); });
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

Exact::Exact(const std::vector<std::pair<std::string, std::string>>& options)
    : ilp(getOptions(options), true), unsatState(false) {
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif
}

void Exact::addVariable(const std::string& name, long long lb, long long ub, const std::string& encoding) {
  if (ilp.getVarFor(name)) throw InvalidArgument("Variable " + name + " already exists.");
  if (encoding != "" && encoding != "order" && encoding != "log" && encoding != "onehot") {
    throw InvalidArgument("Unknown encoding " + encoding +
                          ". Should be \"log\", \"order\" or \"onehot\", or left unspecified.");
  }
  if (unsatState) return;
  try {
    ilp.addVar(name, getCoef(lb), getCoef(ub),
               opt2enc(encoding == "" ? ilp.global.options.ilpEncoding.get() : encoding));
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}

void Exact::addVariable(const std::string& name, const std::string& lb, const std::string& ub,
                        const std::string& encoding) {
  if (ilp.getVarFor(name)) throw InvalidArgument("Variable " + name + " already exists.");
  if (encoding != "" && encoding != "order" && encoding != "log" && encoding != "onehot") {
    throw InvalidArgument("Unknown encoding " + encoding +
                          ". Should be \"log\", \"order\" or \"onehot\", or left unspecified.");
  }
  if (unsatState) return;
  try {
    ilp.addVar(name, getCoef(lb), getCoef(ub),
               opt2enc(encoding == "" ? ilp.global.options.ilpEncoding.get() : encoding));
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}

std::vector<std::string> Exact::getVariables() const {
  return aux::comprehension(ilp.getVariables(), [](IntVar* iv) { return iv->getName(); });
}

void Exact::addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                          long long lb, bool useUB, long long ub) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() > 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addConstraint(IntConstraint{
        getCoefs(coefs), getVariables(vars), {}, aux::option(useLB, getCoef(lb)), aux::option(useUB, getCoef(ub))});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::addConstraint(const std::vector<std::string>& coefs, const std::vector<std::string>& vars, bool useLB,
                          const std::string& lb, bool useUB, const std::string& ub) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() > 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addConstraint(IntConstraint{
        getCoefs(coefs), getVariables(vars), {}, aux::option(useLB, getCoef(lb)), aux::option(useUB, getCoef(ub))});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}

void Exact::addReification(const std::string& head, const std::vector<long long>& coefs,
                           const std::vector<std::string>& vars, long long lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addReification(getVariable(head), IntConstraint{getCoefs(coefs), getVariables(vars), {}, bigint(lb)});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::addReification(const std::string& head, const std::vector<std::string>& coefs,
                           const std::vector<std::string>& vars, const std::string& lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addReification(getVariable(head), IntConstraint{getCoefs(coefs), getVariables(vars), {}, bigint(lb)});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::addRightReification(const std::string& head, const std::vector<long long>& coefs,
                                const std::vector<std::string>& vars, long long lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addRightReification(getVariable(head), IntConstraint{getCoefs(coefs), getVariables(vars), {}, bigint(lb)});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::addRightReification(const std::string& head, const std::vector<std::string>& coefs,
                                const std::vector<std::string>& vars, const std::string& lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addRightReification(getVariable(head), IntConstraint{getCoefs(coefs), getVariables(vars), {}, bigint(lb)});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::addLeftReification(const std::string& head, const std::vector<long long>& coefs,
                               const std::vector<std::string>& vars, long long lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addLeftReification(getVariable(head), IntConstraint{getCoefs(coefs), getVariables(vars), {}, bigint(lb)});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::addLeftReification(const std::string& head, const std::vector<std::string>& coefs,
                               const std::vector<std::string>& vars, const std::string& lb) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
  if (unsatState) return;

  try {
    ilp.addLeftReification(getVariable(head), IntConstraint{getCoefs(coefs), getVariables(vars), {}, bigint(lb)});
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}

void Exact::fix(const std::string& var, long long val) { ilp.fix(getVariable(var), getCoef(val)); }
void Exact::fix(const std::string& var, const std::string& val) { ilp.fix(getVariable(var), getCoef(val)); }

void Exact::setAssumption(const std::string& var, const std::vector<long long>& vals) {
  ilp.setAssumption(getVariable(var), getCoefs(vals));
}
void Exact::setAssumption(const std::string& var, const std::vector<std::string>& vals) {
  ilp.setAssumption(getVariable(var), getCoefs(vals));
}

void Exact::clearAssumptions() { ilp.clearAssumptions(); }
void Exact::clearAssumption(const std::string& var) { ilp.clearAssumption(getVariable(var)); }

bool Exact::hasAssumption(const std::string& var) const { return ilp.hasAssumption(getVariable(var)); }
std::vector<long long> Exact::getAssumption(const std::string& var) const {
  return aux::comprehension(ilp.getAssumption(getVariable(var)),
                            [](const bigint& i) { return static_cast<long long>(i); });
}
std::vector<std::string> Exact::getAssumption_arb(const std::string& var) const {
  return aux::comprehension(ilp.getAssumption(getVariable(var)), [](const bigint& i) { return aux::str(i); });
}

void Exact::setSolutionHints(const std::vector<std::string>& vars, const std::vector<long long>& vals) {
  ilp.setSolutionHints(getVariables(vars), getCoefs(vals));
}
void Exact::setSolutionHints(const std::vector<std::string>& vars, const std::vector<std::string>& vals) {
  ilp.setSolutionHints(getVariables(vars), getCoefs(vals));
}

void Exact::clearSolutionHints(const std::vector<std::string>& vars) { ilp.clearSolutionHints(getVariables(vars)); }

void Exact::boundObjByLastSol() {
  if (unsatState) return;
  try {
    ilp.boundObjByLastSol();
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::invalidateLastSol() {
  if (unsatState) return;
  try {
    ilp.invalidateLastSol();
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}
void Exact::invalidateLastSol(const std::vector<std::string>& vars) {
  if (unsatState) return;
  try {
    ilp.invalidateLastSol(getVariables(vars));
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
  }
}

void Exact::printVariables() const { ilp.printVars(std::cout); }
void Exact::printInput() const { ilp.printInput(std::cout); }
void Exact::printFormula() { ilp.printFormula(std::cout); }

void Exact::setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars, long long offset) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (vars.size() > 1e9) throw InvalidArgument("Objective has more than 1e9 terms.");
  if (unsatState) return;
  ilp.setObjective(getCoefs(coefs), getVariables(vars), {}, offset);
}

void Exact::setObjective(const std::vector<std::string>& coefs, const std::vector<std::string>& vars,
                         const std::string& offset) {
  if (coefs.size() != vars.size()) throw InvalidArgument("Coefficient and variable lists differ in size.");
  if (vars.size() > 1e9) throw InvalidArgument("Objective has more than 1e9 terms.");
  if (unsatState) return;
  ilp.setObjective(getCoefs(coefs), getVariables(vars), {}, getCoef(offset));
}

SolveState Exact::runOnce() {
  if (unsatState) return SolveState::UNSAT;
  SolveState state = ilp.runOnce(false);
  unsatState = state == SolveState::UNSAT;
  return state;
}

SolveState Exact::runFull(bool optimize, double timeout) {
  if (unsatState) return SolveState::UNSAT;
  return ilp.runFull(optimize, timeout);
}

std::pair<long long, long long> Exact::getObjectiveBounds() const {
  return {static_cast<long long>(ilp.getLowerBound()), static_cast<long long>(ilp.getUpperBound())};
}
std::pair<std::string, std::string> Exact::getObjectiveBounds_arb() const {
  return {aux::str(ilp.getLowerBound()), aux::str(ilp.getUpperBound())};
}

bool Exact::hasSolution() const { return ilp.hasSolution(); }

std::vector<long long> Exact::getLastSolutionFor(const std::vector<std::string>& vars) const {
  if (!ilp.hasSolution()) throw InvalidArgument("No solution can be returned if no solution has been found.");
  return aux::comprehension(ilp.getLastSolutionFor(getVariables(vars)),
                            [](const bigint& i) { return static_cast<long long>(i); });
}
std::vector<std::string> Exact::getLastSolutionFor_arb(const std::vector<std::string>& vars) const {
  return aux::comprehension(ilp.getLastSolutionFor(getVariables(vars)), [](const bigint& i) { return aux::str(i); });
}

bool Exact::hasCore() const { return unsatState || ilp.hasCore(); }

std::vector<std::string> Exact::getLastCore() {
  if (unsatState) return {};
  return aux::comprehension(ilp.getLastCore(), [](IntVar* iv) { return iv->getName(); });
}

void Exact::printStats() { quit::printFinalStats(ilp); }

std::vector<std::pair<long long, long long>> Exact::propagate(const std::vector<std::string>& vars, double timeout) {
  if (unsatState) return {};
  try {
    return aux::comprehension(ilp.propagate(getVariables(vars), timeout), [](const std::pair<bigint, bigint>& x) {
      return std::pair<long long, long long>(static_cast<long long>(x.first), static_cast<long long>(x.second));
    });
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
    return {};
  }
}
std::vector<std::pair<std::string, std::string>> Exact::propagate_arb(const std::vector<std::string>& vars,
                                                                      double timeout) {
  if (unsatState) return {};
  try {
    return aux::comprehension(ilp.propagate(getVariables(vars), timeout), [](const std::pair<bigint, bigint>& x) {
      return std::pair<std::string, std::string>(aux::str(x.first), aux::str(x.second));
    });
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
    return {};
  }
}

std::vector<std::vector<long long>> Exact::pruneDomains(const std::vector<std::string>& vars, double timeout) {
  if (unsatState) return std::vector<std::vector<long long>>(vars.size());
  try {
    return aux::comprehension(ilp.pruneDomains(getVariables(vars), timeout), [](const std::vector<bigint>& x) {
      return aux::comprehension(x, [](const bigint& y) { return static_cast<long long>(y); });
    });
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
    return std::vector<std::vector<long long>>(vars.size());
  }
}
std::vector<std::vector<std::string>> Exact::pruneDomains_arb(const std::vector<std::string>& vars, double timeout) {
  if (unsatState) return std::vector<std::vector<std::string>>(vars.size());
  try {
    return aux::comprehension(ilp.pruneDomains(getVariables(vars), timeout), [](const std::vector<bigint>& x) {
      return aux::comprehension(x, [](const bigint& y) { return aux::str(y); });
    });
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
    return std::vector<std::vector<std::string>>(vars.size());
  }
}

long long Exact::count(const std::vector<std::string>& vars, double timeout) {
  if (unsatState) return 0;
  try {
    return ilp.count(getVariables(vars), timeout);
  } catch (const UnsatEncounter& ue) {
    unsatState = true;
    return 0;
  }
}
