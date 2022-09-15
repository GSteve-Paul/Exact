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

#include "quit.hpp"
#include <iostream>
#include "ILP.hpp"
#include "Optimization.hpp"
#include "Solver.hpp"
#include "auxiliary.hpp"
#include "globals.hpp"

namespace xct {

void quit::printLits(const std::vector<Lit>& lits, char pre, bool onlyPositive) {
  std::cout << pre;
  for (Lit l : lits) {
    if (l == 0 || (onlyPositive && l < 0)) continue;
    std::cout << " " << l;
  }
  std::cout << std::endl;
}

void quit::printLitsMaxsat(const std::vector<Lit>& lits, const ILP& ilp) {
  std::cout << "v ";
  for (Var v = 1; v <= ilp.getMaxSatVars(); ++v) {
    std::cout << (lits[v] > 0);
  }
  std::cout << std::endl;
}

void quit::printFinalStats(ILP& ilp) {
  if (options.printUnits) printLits(ilp.getSolver().getUnits(), 'u', false);
  if (options.verbosity.get() > 0) stats.print();
  if (options.printCsvData) stats.printCsvLine();
  if (options.printOpb) ilp.printFormula();
}

void quit::exit_SUCCESS(ILP& ilp) {
  if (logger) logger->flush();
  printFinalStats(ilp);
  bool asMiplib = options.fileFormat.is("mps") || options.fileFormat.is("lp");
  if (ilp.hasSolution()) {
    if (asMiplib) {
      std::cout << "=obj= " << ilp.getUpperBound() << std::endl;
      if (options.printSol) ilp.printOrigSol();
    } else if (options.fileFormat.is("wcnf")) {
      std::cout << "o " << ilp.getUpperBound() << "\n";
      std::cout << "s OPTIMUM FOUND" << std::endl;
      if (options.printSol) printLitsMaxsat(ilp.getSolver().getLastSolution(), ilp);
    } else {
      std::cout << "o " << ilp.getUpperBound() << "\n";
      std::cout << "s OPTIMUM FOUND" << std::endl;
      if (options.printSol) printLits(ilp.getSolver().getLastSolution(), 'v', true);
    }
    xct::aux::flushexit(30);
  } else {
    std::cout << (asMiplib ? "=infeas=" : "s UNSATISFIABLE") << std::endl;
    xct::aux::flushexit(20);
  }
}

void quit::exit_INDETERMINATE(ILP& ilp) {
  if (logger) logger->flush();
  printFinalStats(ilp);
  bool asMiplib = options.fileFormat.is("mps") || options.fileFormat.is("lp");
  if (ilp.hasSolution()) {
    if (asMiplib) {
      std::cout << "=obj= " << ilp.getUpperBound() << std::endl;
      if (options.printSol) ilp.printOrigSol();
    } else if (options.fileFormat.is("wcnf")) {
      std::cout << "o " << ilp.getUpperBound() << "\n";
      std::cout << "s UNKNOWN" << std::endl;
      if (options.printSol) printLitsMaxsat(ilp.getSolver().getLastSolution(), ilp);
    } else {
      std::cout << "c best so far " << ilp.getUpperBound() << "\n";
      std::cout << "s SATISFIABLE" << std::endl;
      if (options.printSol) printLits(ilp.getSolver().getLastSolution(), 'v', true);
    }
    xct::aux::flushexit(10);
  } else {
    if (!options.noSolve) {
      std::cout << (asMiplib ? "=unkn=" : "s UNKNOWN") << std::endl;
    }
    xct::aux::flushexit(0);
  }
}

void quit::exit_ERROR(const std::initializer_list<std::string>& messages) {
  std::cout << "Error: ";
  for (const std::string& m : messages) std::cout << m;
  std::cout << std::endl;
  xct::aux::flushexit(1);
}

void quit::checkInterrupt() {
  if (asynch_interrupt || (options.timeout.get() > 0 && stats.getTime() > options.timeout.get()) ||
      (options.timeoutDet.get() > 0 && stats.getDetTime() > options.timeoutDet.get())) {
    throw asynchInterrupt;
  }
}

}  // namespace xct
