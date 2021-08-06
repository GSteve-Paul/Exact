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

#include "Exact.hpp"
#include <fstream>
#include "Optimization.hpp"
#include "globals.hpp"
#include "parsing.hpp"

int main(int argc, char** argv) {
  rs::stats.STARTTIME.z = rs::aux::cpuTime();
  rs::asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  rs::options.parseCommandLine(argc, argv);

  rs::aux::rng::seed = rs::options.randomSeed.get();

  if (rs::options.verbosity.get() > 0) {
    std::cout << "c Exact 2021\n";
    std::cout << "c branch " << EXPANDED(GIT_BRANCH) << "\n";
    std::cout << "c commit " << EXPANDED(GIT_COMMIT_HASH) << std::endl;
  }

  if (!rs::options.proofLog.get().empty()) {
    rs::logger = std::make_shared<rs::Logger>(rs::options.proofLog.get());
    rs::cePools.initializeLogging(rs::logger);
  }

  rs::aux::timeCallVoid([&] { rs::parsing::file_read(rs::ilp); }, rs::stats.PARSETIME);

  if (rs::options.noSolve) {
    rs::quit::exit_INDETERMINATE(rs::ilp);
  }
  if (rs::options.printCsvData) {
    rs::stats.printCsvHeader();
  }
  if (rs::options.verbosity.get() > 0) {
    std::cout << "c " << rs::ilp.solver.getNbOrigVars() << " vars " << rs::ilp.solver.getNbConstraints() << " constrs"
              << std::endl;
  }

  rs::stats.RUNSTARTTIME.z = rs::aux::cpuTime();

  State res;
  rs::ilp.init();
  try {
    res = rs::ilp.run();
  } catch (const rs::AsynchronousInterrupt& ai) {
    if (rs::options.outputMode.is("default")) {
      std::cout << "c " << ai.what() << std::endl;
    }
    res = State::FAIL;
  }

  if (res == State::FAIL) {
    rs::quit::exit_INDETERMINATE(rs::ilp);
  } else {
    rs::quit::exit_SUCCESS(rs::ilp);
  }
}
