/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "PublicInterface.hpp"
#include <csignal>
#include "globals.hpp"
#include "parsing.hpp"
#include "run.hpp"

void run() {
  rs::stats.STARTTIME.z = rs::aux::cpuTime();
  rs::asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  rs::aux::rng::seed = rs::options.randomSeed.get();

  rs::options.printOpb.parse("");
  // rs::options.noSolve.parse("");
  rs::options.verbosity.parse("0");

  if (!rs::options.proofLog.get().empty()) {
    rs::logger = std::make_shared<rs::Logger>(rs::options.proofLog.get());
    rs::cePools.initializeLogging(rs::logger);
  }

  State res = rs::run::run();
  if (res == State::FAIL) {
    rs::quit::exit_INDETERMINATE(rs::run::solver);
  } else {
    rs::quit::exit_SUCCESS(rs::run::solver);
  }
}

State addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB, long long lb,
                    bool useUB, long long ub) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9) return State::FAIL;
  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<rs::IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(rs::run::solver.ilp.getVarFor(vars[i]));
  }

  return rs::run::solver.ilp.addConstraint(cfs, vs, {}, rs::aux::optional(useLB, lb), rs::aux::optional(useUB, ub));
}

State setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9 || rs::run::solver.ilp.hasObjective()) return State::FAIL;

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<rs::IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(rs::run::solver.ilp.getVarFor(vars[i]));
  }

  rs::run::solver.ilp.addObjective(cfs, vs, {});
  return State::SUCCESS;
}
