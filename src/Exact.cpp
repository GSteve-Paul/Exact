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
  stats.STARTTIME.z = aux::cpuTime();

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  options.parseCommandLine(argc, argv);

  if (options.verbosity.get() > 0) {
    std::cout << "c Exact 2021\n";
    std::cout << "c branch " << EXPANDED(GIT_BRANCH) << "\n";
    std::cout << "c commit " << EXPANDED(GIT_COMMIT_HASH) << std::endl;
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
    std::cout << "c " << ilp.getSolver().getNbOrigVars() << " vars " << ilp.getSolver().getNbConstraints() << " constrs"
              << std::endl;
  }

  stats.RUNSTARTTIME.z = aux::cpuTime();

  ilp.init(false);
  SolveState res = SolveState::INPROCESSED;
  while (res == SolveState::INPROCESSED || res == SolveState::SAT) {
    res = ilp.run();
  }
  if (res == SolveState::INTERRUPTED) {
    quit::exit_INDETERMINATE(ilp);
  } else {
    quit::exit_SUCCESS(ilp);
  }
}

Exact::Exact() : ilp() {
  stats.STARTTIME.z = aux::cpuTime();

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  if (!options.proofLog.get().empty()) {
    logger = std::make_shared<Logger>(options.proofLog.get());
    cePools.initializeLogging(logger);
  }
}

State Exact::addVariable(const std::string& name, long long lb, long long ub) {
  if (ilp.hasVarFor(name)) return State::FAIL;
  ilp.getVarFor(name, false, lb, ub);
  return State::SUCCESS;
}

std::vector<std::string> Exact::getVariables() const { return ilp.getVariables(); }

State Exact::addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                           long long lb, bool useUB, long long ub) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9) {
    // TODO: error messages for fails...
    std::cerr << "Incorrect number of coefficients " << coefs.size() << std::endl;
    return State::FAIL;
  }
  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    if (!ilp.hasVarFor(vars[i])) {
      std::cerr << "No known variable " << vars[i] << std::endl;
      return State::FAIL;
    }
    cfs.push_back(coefs[i]);
    vs.push_back(ilp.getVarFor(vars[i]));
  }

  return ilp.addConstraint(cfs, vs, {}, aux::optional(useLB, lb), aux::optional(useUB, ub));
}

State Exact::setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars) {
  if (coefs.size() != vars.size() || vars.size() >= 1e9 || ilp.getOptimization()) return State::FAIL;

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    if (!ilp.hasVarFor(vars[i])) return State::FAIL;
    cfs.push_back(coefs[i]);
    vs.push_back(ilp.getVarFor(vars[i]));
  }

  ilp.setObjective(cfs, vs, {});
  return State::SUCCESS;
}

State Exact::setAssumptions(const std::vector<std::string>& vars, const std::vector<long long>& vals) {
  if (vals.size() != vars.size() || vars.size() >= 1e9) return State::FAIL;
  std::vector<bigint> values;
  values.reserve(vars.size());
  std::vector<IntVar*> vs;
  vs.reserve(vars.size());
  for (int i = 0; i < (int)vars.size(); ++i) {
    if (!ilp.hasVarFor(vars[i])) return State::FAIL;
    vs.push_back(ilp.getVarFor(vars[i]));
    values.push_back(vals[i]);
    if (values.back() > vs.back()->getUpperBound() || values.back() < vs.back()->getLowerBound()) return State::FAIL;
  }
  ilp.setAssumptions(values, vs);
  return State::SUCCESS;
}

State Exact::addLastSolObjectiveBound() { return ilp.addLastSolObjectiveBound(); }
State Exact::addLastSolInvalidatingClause() { return ilp.addLastSolInvalidatingClause(); }

void Exact::printFormula() { ilp.printFormula(); }

void Exact::init(bool onlyFormulaDerivations) {
  ilp.init(onlyFormulaDerivations);

  stats.RUNSTARTTIME.z = aux::cpuTime();
}

SolveState Exact::run() { return ilp.run(); }

long long Exact::getLowerBound() const {
  assert(ilp.multIsOne());
  return static_cast<long long>(ilp.getLowerBound());
}

long long Exact::getUpperBound() const {
  assert(ilp.multIsOne());
  return static_cast<long long>(ilp.getUpperBound());
}

bool Exact::hasSolution() const { return ilp.hasSolution(); }

std::vector<long long> Exact::getLastSolutionFor(const std::vector<std::string>& vars) const {
  if (!hasSolution()) return {};
  return ilp.getLastSolutionFor(vars);
}

bool Exact::hasCore() const { return ilp.hasCore(); }

std::vector<std::string> Exact::getLastCore() const {
  if (!hasCore()) return {};
  return ilp.getLastCore();
}
