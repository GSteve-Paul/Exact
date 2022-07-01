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

#include "Exact.hpp"
#include <fstream>
#include "ILP.hpp"
#include "globals.hpp"
#include "parsing.hpp"

using namespace xct;

int main(int argc, char** argv) {
  stats.startTime = std::chrono::steady_clock::now();

  signal(SIGINT, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  options.parseCommandLine(argc, argv);

  if (options.verbosity.get() > 0) {
    std::cout << "c Exact - branch " EXPANDED(GIT_BRANCH) " commit " EXPANDED(GIT_COMMIT_HASH) << std::endl;
  }

  if (!options.proofLog.get().empty()) {
    logger = std::make_shared<Logger>(options.proofLog.get());
    cePools.initializeLogging(logger);
  }

  ILP ilp;

  aux::timeCallVoid([&] { parsing::file_read(ilp); }, stats.PARSETIME);

  if (options.noSolve) quit::exit_INDETERMINATE(ilp);
  if (options.printCsvData) stats.printCsvHeader();
  if (options.verbosity.get() > 0) {
    std::cout << "c " << ilp.getSolver().getNbVars() << " vars " << ilp.getSolver().getNbConstraints() << " constrs"
              << std::endl;
  }

  stats.runStartTime = std::chrono::steady_clock::now();

  ilp.init(true, true);
  SolveState res = SolveState::INPROCESSED;
  try {
    while (res == SolveState::INPROCESSED || res == SolveState::SAT) {
      res = ilp.run();
    }
    quit::exit_SUCCESS(ilp);
  } catch (const AsynchronousInterrupt& ai) {
    if (options.outputMode.is("default")) std::cout << "c " << ai.what() << std::endl;
    quit::exit_INDETERMINATE(ilp);
  }
}

xct::IntVar* Exact::getVariable(const std::string& name) {
  if (!ilp.hasVarFor(name)) throw std::invalid_argument("No variable " + name + " found.");
  return ilp.getVarFor(name);
}

Exact::Exact() : ilp() {
  stats.startTime = std::chrono::steady_clock::now();

  signal(SIGINT, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  if (!options.proofLog.get().empty()) {
    logger = std::make_shared<Logger>(options.proofLog.get());
    cePools.initializeLogging(logger);
  }
}

void Exact::addVariable(const std::string& name, long long lb, long long ub) {
  if (ilp.hasVarFor(name)) throw std::invalid_argument("Variable " + name + " already exists.");
  ilp.getVarFor(name, false, lb, ub);
}

std::vector<std::string> Exact::getVariables() const { return ilp.getVariables(); }

State Exact::addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                           long long lb, bool useUB, long long ub) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() > 1e9) throw std::invalid_argument("Constraint has more than 1e9 terms.");
  if (ilp.unsatState()) return State::UNSAT;

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(getVariable(vars[i]));
  }

  return ilp.addConstraint(cfs, vs, {}, aux::option(useLB, lb), aux::option(useUB, ub));
}

State Exact::addReification(const std::string& head, const std::vector<long long>& coefs,
                            const std::vector<std::string>& vars, long long lb) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw std::invalid_argument("Constraint has more than 1e9 terms.");
  if (ilp.unsatState()) return State::UNSAT;

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(getVariable(vars[i]));
  }

  return ilp.addReification(getVariable(head), cfs, vs, bigint(lb));
}

void Exact::setAssumptions(const std::vector<std::string>& vars, const std::vector<long long>& vals) {
  if (vals.size() != vars.size()) throw std::invalid_argument("Value and variable lists differ in size.");
  if (vars.size() > 1e9) throw std::invalid_argument("More than 1e9 assumptions.");
  if (ilp.unsatState()) return;

  std::vector<bigint> values;
  values.reserve(vars.size());
  std::vector<IntVar*> vs;
  vs.reserve(vars.size());
  for (int i = 0; i < (int)vars.size(); ++i) {
    vs.push_back(getVariable(vars[i]));
    values.push_back(vals[i]);
    if (values.back() > vs.back()->getUpperBound() || values.back() < vs.back()->getLowerBound())
      throw std::invalid_argument("Value for " + vars[i] + " exceeds variable bounds.");
  }
  ilp.setAssumptions(values, vs);
}

State Exact::boundObjByLastSol() {
  if (ilp.unsatState()) return State::UNSAT;
  return ilp.boundObjByLastSol();
}
State Exact::invalidateLastSol() {
  if (ilp.unsatState()) return State::UNSAT;
  return ilp.invalidateLastSol();
}
State Exact::invalidateLastSol(const std::vector<std::string>& vars) {
  if (ilp.unsatState()) return State::UNSAT;
  return ilp.invalidateLastSol(vars);
}

void Exact::printFormula() { ilp.printFormula(); }

void Exact::init(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool boundObjective,
                 bool addNonImplieds) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (vars.size() > 1e9) throw std::invalid_argument("Objective has more than 1e9 terms.");

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(getVariable(vars[i]));
  }
  ilp.setObjective(cfs, vs, {});

  ilp.init(boundObjective, addNonImplieds);

  stats.runStartTime = std::chrono::steady_clock::now();
}

SolveState Exact::run() {
  if (ilp.unsatState()) return SolveState::UNSAT;
  return ilp.run();
}

std::pair<long long, long long> Exact::getObjectiveBounds() const {
  return {static_cast<long long>(ilp.getLowerBound()), static_cast<long long>(ilp.getUpperBound())};
}

std::pair<long long, long long> Exact::getBounds(const std::string& var) const {
  if (!ilp.hasVarFor(var)) throw std::invalid_argument("No variable " + var + " found.");
  return static_cast<std::pair<long long, long long>>(ilp.getBounds(var));
}

bool Exact::hasSolution() const { return ilp.hasSolution(); }

std::vector<long long> Exact::getLastSolutionFor(const std::vector<std::string>& vars) const {
  return aux::cast_vec<long long, bigint>(ilp.getLastSolutionFor(vars));
}

bool Exact::hasCore() const { return ilp.hasCore(); }

std::vector<std::string> Exact::getLastCore() const { return ilp.getLastCore(); }

void Exact::printStats() { quit::printFinalStats(ilp); }

void Exact::setVerbosity(int verbosity) { options.verbosity.parse(std::to_string(verbosity)); }

std::vector<std::pair<long long, long long>> Exact::propagate(const std::vector<std::string>& varnames) {
  if (ilp.unsatState()) {
    throw std::runtime_error("Propagation is undefined for unsatisfiable problems.");
  }
  std::vector<std::pair<long long, long long>> result;
  result.reserve(varnames.size());
  for (const std::pair<bigint, bigint>& tmp : ilp.propagate(varnames)) {
    result.emplace_back(static_cast<long long>(tmp.first), static_cast<long long>(tmp.second));
  }
  return result;
}
