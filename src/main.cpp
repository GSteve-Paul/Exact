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

#include <csignal>
#include "ILP.hpp"
#include "quit.hpp"

using namespace xct;

void runOnce(int argc, char** argv, ILP& ilp) {
  ilp.global.stats.startTime = std::chrono::steady_clock::now();
  ilp.global.options.parseCommandLine(argc, argv);
  ilp.global.logger.activate(ilp.global.options.proofLog.get());

  if (ilp.global.options.verbosity.get() > 0) {
    std::cout << "c Exact - branch " EXPANDED(GIT_BRANCH) " commit " EXPANDED(GIT_COMMIT_HASH) << std::endl;
  }

  aux::timeCallVoid([&] { parsing::file_read(ilp); }, ilp.global.stats.PARSETIME);

  if (ilp.global.options.noSolve) throw AsynchronousInterrupt();
  if (ilp.global.options.printCsvData) ilp.global.stats.printCsvHeader();
  if (ilp.global.options.verbosity.get() > 0) {
    std::cout << "c " << ilp.getSolver().getNbVars() << " vars " << ilp.getSolver().getNbConstraints() << " constrs"
              << std::endl;
  }

  ilp.global.stats.runStartTime = std::chrono::steady_clock::now();

  ilp.init();
  SolveState res = SolveState::INPROCESSED;

  while (res == SolveState::INPROCESSED || res == SolveState::SAT) {
    res = ilp.runOnce();
  }
}

int main(int argc, char** argv) {
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  ILP ilp;
  try {
    runOnce(argc, argv, ilp);
  } catch (const AsynchronousInterrupt& ai) {
    std::cout << "c " << ai.what() << std::endl;
    return quit::exit_INDETERMINATE(ilp);
  } catch (const UnsatEncounter& ue) {
    return quit::exit_SUCCESS(ilp);
  } catch (const std::invalid_argument& ia) {
    return quit::exit_ERROR(ia.what());
  } catch (const EarlyTermination& et) {
    return quit::exit_EARLY();
  }
  return quit::exit_SUCCESS(ilp);
}