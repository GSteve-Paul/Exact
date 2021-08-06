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
#include "aux.hpp"
#include "globals.hpp"

namespace rs {

void quit::printLits(const std::vector<Lit>& lits, char pre, bool onlyPositive) {
  std::cout << pre;
  for (Lit l : lits) {
    if (l == 0 || (onlyPositive && l < 0)) continue;
    std::cout << " " << l;
  }
  std::cout << std::endl;
}

void quit::printLitsMaxsat(const std::vector<Lit>& lits, const Solver& solver) {
  std::cout << "v ";
  if (options.outputMode.is("maxsatnew")) {
    for (Var v = 1; v <= solver.maxSatVars; ++v) {
      std::cout << (lits[v] > 0);
    }
  } else {
    assert(options.outputMode.is("maxsat"));
    for (Var v = 1; v <= solver.maxSatVars; ++v) {
      std::cout << lits[v] << " ";
    }
  }
  std::cout << std::endl;
}

void quit::printFormula(Solver& solver) {
  int nbConstraints = 0;
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    nbConstraints +=
        c.getOrigin() == Origin::FORMULA && !c.isMarkedForDelete() && !c.isSatisfiedAtRoot(solver.getLevel());
  }
  std::cout << "* #variable= " << solver.getNbOrigVars() << " #constraint= " << nbConstraints << "\n";
  if (rs::ilp.hasObjective()) {
    std::cout << "min: ";
    for (const IntTerm& it : rs::ilp.obj.getLhs()) {
      std::cout << (it.c < 0 ? "" : "+") << it.c << " x" << it.v->getName() << " ";
    }
    std::cout << ";\n";
  }
  for (Lit l : solver.getUnits()) {
    if (toVar(l) > solver.getNbOrigVars()) continue;
    std::cout << std::pair<int, Lit>{1, l} << " >= 1 ;\n";
  }
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    if (c.getOrigin() == Origin::FORMULA && !c.isMarkedForDelete() && !c.isSatisfiedAtRoot(solver.getLevel())) {
      CeSuper ce = c.toExpanded(cePools);
      ce->toStreamAsOPB(std::cout);
      std::cout << "\n";
    }
  }
}

void quit::printFinalStats(Solver& solver) {
  if (options.verbosity.get() > 0) stats.print();
  if (options.printCsvData) stats.printCsvLine();
  if (options.printOpb) printFormula(solver);
}

void quit::exit_SUCCESS(ILP& ilp) {
  if (logger) logger->flush();
  if (options.printUnits) printLits(ilp.solver.getUnits(), 'u', false);
  if (ilp.hasSolution()) {
    if (options.outputMode.is("miplib")) {
      std::cout << "=obj= " << ilp.getUpperBound() << "\n";
      rs::ilp.printOrigSol(ilp.solver.getLastSolution());
    }
    if (options.outputMode.is("maxsat") || options.outputMode.is("maxsatnew")) {
      printFinalStats(ilp.solver);
      std::cout << "o " << ilp.getUpperBound() << "\n";
      std::cout << "s OPTIMUM FOUND" << std::endl;
      printLitsMaxsat(ilp.solver.getLastSolution(), ilp.solver);
    } else {
      if (options.printSol) printLits(ilp.solver.getLastSolution(), 'v', true);
      printFinalStats(ilp.solver);
      std::cout << "o " << ilp.getUpperBound() << "\n";
      std::cout << "s OPTIMUM FOUND" << std::endl;
    }
    rs::aux::flushexit(30);
  } else {
    if (options.outputMode.is("miplib")) {
      std::cout << "=infeas=\n";
    }
    printFinalStats(ilp.solver);
    std::cout << "s UNSATISFIABLE" << std::endl;
    rs::aux::flushexit(20);
  }
}

void quit::exit_INDETERMINATE(ILP& ilp) {
  if (logger) logger->flush();
  if (options.printUnits) printLits(ilp.solver.getUnits(), 'u', false);
  if (ilp.hasSolution()) {
    if (options.outputMode.is("miplib")) {
      std::cout << "=obj= " << ilp.getUpperBound() << "\n";
      rs::ilp.printOrigSol(ilp.solver.getLastSolution());
    }
    if (options.outputMode.is("maxsat") || options.outputMode.is("maxsatnew")) {
      printFinalStats(ilp.solver);
      std::cout << "o " << ilp.getUpperBound() << "\n";
      std::cout << "s UNKNOWN" << std::endl;
      printLitsMaxsat(ilp.solver.getLastSolution(), ilp.solver);
    } else {
      if (options.printSol) printLits(ilp.solver.getLastSolution(), 'v', true);
      printFinalStats(ilp.solver);
      std::cout << "c best so far " << ilp.getUpperBound() << "\n";
      std::cout << "s SATISFIABLE" << std::endl;
    }
    rs::aux::flushexit(10);
  } else {
    if (options.outputMode.is("miplib")) {
      std::cout << "=unkn=\n";
    }
    printFinalStats(ilp.solver);
    if (!options.noSolve) std::cout << "s UNKNOWN" << std::endl;
    rs::aux::flushexit(0);
  }
}

void quit::exit_ERROR(const std::initializer_list<std::string>& messages) {
  std::cout << "Error: ";
  for (const std::string& m : messages) std::cout << m;
  std::cout << std::endl;
  rs::aux::flushexit(1);
}

void quit::checkInterrupt() {
  if (asynch_interrupt || (options.timeout.get() > 0 && stats.getTime() > options.timeout.get()) ||
      (options.timeoutDet.get() > 0 && stats.getDetTime() > options.timeoutDet.get())) {
    throw asynchInterrupt;
  }
}

}  // namespace rs
