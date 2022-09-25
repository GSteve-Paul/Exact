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
#include "fodot/Expression.hpp"
#include "fodot/Fodot.hpp"
#include "fodot/IneqExpr.hpp"
#include "fodot/Theory.hpp"
#include "quit.hpp"

using namespace xct;

void runOnce(int argc, char** argv, ILP& ilp) {
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
}

int main(int argc, char** argv) {
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  //  ILP ilp;
  //  try {
  //    runOnce(argc, argv, ilp);
  //  } catch (const AsynchronousInterrupt& ai) {
  //    std::cout << "c " << ai.what() << std::endl;
  //    return quit::exit_INDETERMINATE(ilp);
  //  } catch (const UnsatEncounter& ue) {
  //    return quit::exit_SUCCESS(ilp);
  //  } catch (const std::invalid_argument& ia) {
  //    return quit::exit_ERROR(ia.what());
  //  } catch (const EarlyTermination& et) {
  //    return quit::exit_EARLY();
  //  }
  //  return quit::exit_SUCCESS(ilp);

  fodot::Theory theo;

  theo.addMijnCollega();

  ILP ilp(true);

  theo.addTo(ilp, false, "1");
  // std::cout << theo << std::endl;

  ilp.init(true, true);

  std::ofstream output("/tmp/mijncollega.opb");
  if (output.is_open()) {
    ilp.printFormula(output);
    output.close();
  } else {
    std::cerr << "Unable to open file" << std::endl;
  }

  SolveState res = ilp.runFull(theo.objective != nullptr, 10);

  std::cout << "RESULT: " << res << std::endl;
  if (ilp.hasSolution()) {
    theo.getModelMC(ilp, "/tmp/mijncollega.csv");
  } else if (ilp.hasCore()) {
    for (const IntVar* iv : ilp.getLastCore()) {
      std::cout << iv->getName() << std::endl;
    }
  } else {
    std::cout << "NO INFO" << std::endl;
  }

  ILP ilp2(true);
  std::vector<fodot::DomEl> unknowns = theo.fixToegewezen("Gino");
  std::cout << "UNKNOWNS: " << unknowns << std::endl;
  theo.addTo(ilp2, false, "2");
  ilp2.init(false, true);
  std::vector<IntVar*> toRepair;
  std::vector<fodot::Tup> args;
  fodot::DomEl gino("Gino");
  for (const fodot::DomEl& dienst : unknowns) {
    fodot::Functor& toegewezen = *theo.voc.getFunctor("toegewezen");
    for (const fodot::DomEl& dokter : toegewezen.range) {
      IntVar* atom = ilp2.getVarFor(fodot::Terminal(toegewezen, {dienst, dokter}).getRepr());
      assert(atom);
      if (dokter == gino) {
        ilp2.fix(atom, 0);
      } else {
        args.push_back({dokter, dienst});
        toRepair.push_back(atom);
      }
    }
  }
  auto bounds = ilp2.propagate(toRepair);
  fodot::Functor& voorkeur = *theo.voc.getFunctor("voorkeur");
  for (int i = 0; i < (int)toRepair.size(); ++i) {
    if (bounds[i].second == 1) {
      std::cout << args[i][0] << " kan " << args[i][1] << " opnemen met voorkeur " << voorkeur.getInter(args[i])
                << std::endl;
    }
  }

  //  SolveState res2 = ilp2.runFull(false, 10);
  //  std::cout << "RESULT: " << res2 << std::endl;
  //  std::cout << "TEST " << ilp2.hasSolution() << std::endl;
  //  if (ilp2.hasSolution()) {
  //    theo.getModelMC(ilp2, "/tmp/mijncollega_repaired.csv");
  //  } else {
  //    std::cout << "No second solution, timeout too low?" << std::endl;
  //  }
}