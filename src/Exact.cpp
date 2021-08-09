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
  asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  options.parseCommandLine(argc, argv);

  aux::rng::seed = options.randomSeed.get();

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

  ilp.init();
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

Exact::Exact() {
  stats.STARTTIME.z = aux::cpuTime();
  asynch_interrupt = false;
  aux::rng::seed = options.randomSeed.get();

  ilp = std::make_unique<ILP>();

  options.printOpb.parse("");
  // options.noSolve.parse("");
  options.verbosity.parse("0");

  if (!options.proofLog.get().empty()) {
    logger = std::make_shared<Logger>(options.proofLog.get());
    cePools.initializeLogging(logger);
  }
}

void Exact::init() {
  ilp->init();
  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  stats.RUNSTARTTIME.z = aux::cpuTime();
}

State Exact::addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                           long long lb, bool useUB, long long ub) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9) return State::FAIL;
  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(ilp->getVarFor(vars[i]));
  }

  return ilp->addConstraint(cfs, vs, {}, aux::optional(useLB, lb), aux::optional(useUB, ub));
}

State Exact::setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9 || ilp->getOptimization()) return State::FAIL;

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(ilp->getVarFor(vars[i]));
  }

  ilp->setObjective(cfs, vs, {});
  return State::SUCCESS;
}

SolveState Exact::run() { return ilp->run(); }
