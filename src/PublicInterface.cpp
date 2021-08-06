/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "PublicInterface.hpp"
#include <csignal>
#include "ILP.hpp"
#include "Optimization.hpp"
#include "globals.hpp"
#include "parsing.hpp"

xct::ILP public_ilp;

void run() {
  xct::stats.STARTTIME.z = xct::aux::cpuTime();
  xct::asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  xct::aux::rng::seed = xct::options.randomSeed.get();

  xct::options.printOpb.parse("");
  // xct::options.noSolve.parse("");
  xct::options.verbosity.parse("0");

  if (!xct::options.proofLog.get().empty()) {
    xct::logger = std::make_shared<xct::Logger>(xct::options.proofLog.get());
    xct::cePools.initializeLogging(xct::logger);
  }

  xct::stats.RUNSTARTTIME.z = xct::aux::cpuTime();
  State res;
  public_ilp.init();
  try {
    res = public_ilp.run();
  } catch (const xct::AsynchronousInterrupt& ai) {
    if (xct::options.outputMode.is("default")) {
      std::cout << "c " << ai.what() << std::endl;
    }
    res = State::FAIL;
  }

  if (res == State::FAIL) {
    xct::quit::exit_INDETERMINATE(public_ilp);
  } else {
    xct::quit::exit_SUCCESS(public_ilp);
  }
}

State addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB, long long lb,
                    bool useUB, long long ub) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9) return State::FAIL;
  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<xct::IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(public_ilp.getVarFor(vars[i]));
  }

  return public_ilp.addConstraint(cfs, vs, {}, xct::aux::optional(useLB, lb), xct::aux::optional(useUB, ub));
}

State setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars) {
  if (coefs.size() != vars.size() || coefs.size() >= 1e9 || public_ilp.hasObjective()) return State::FAIL;

  std::vector<bigint> cfs;
  cfs.reserve(coefs.size());
  std::vector<xct::IntVar*> vs;
  vs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    cfs.push_back(coefs[i]);
    vs.push_back(public_ilp.getVarFor(vars[i]));
  }

  public_ilp.addObjective(cfs, vs, {});
  return State::SUCCESS;
}
