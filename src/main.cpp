/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2023 Jo Devriendt, Nonfiction Software

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
#include "constraints/ConstrExpPools.hpp"
#include "constraints/ConstrExp.hpp"
#include "constraints/Constr.hpp"
#include "constraints/ConstrSimple.hpp"
#include "auxiliary.hpp"

using namespace xct;

int main(int argc, char** argv) {

  // Global global;
  // ConstrExp32 ce32(global);

  // global.cePools.resize(5);

  // Ce32 constr = global.cePools.take32();

  // // configure using addLhs and addRhs
  // constr->addLhs(2, 1);
  // constr->addLhs(3, 2);
  // constr->addLhs(1, 3);
  // constr->addLhs(4, 4);

  // constr->addRhs(8);

  // constr->toStreamPure(std::cout);
  // std::cout << "\n weaken first lit: " << std::endl;

  // constr->weaken(1);

  // constr->toStreamPure(std::cout);
  // std::cout << "\n restore: " << std::endl;

  // constr->addLhs(2, 1);
  // constr->addRhs(2);

  // constr->toStreamPure(std::cout);
  // std::cout << "\n weaken superfluous: " << std::endl;

  // // decide(1);

  // constr->weakenSuperfluous(2, false, []([[maybe_unused]] Var v) { return true; });
  // // std::cout << "\n divide by 2 and round up: " << std::endl;

  // // constr->divideRoundUp(2);

  // constr->toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;

  // for (int i = 5; i > 0; i--) {
  //   std::cout << i << " ";
  // }

  // return 0;

  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  ILP ilp;
  try {
    ilp.runInternal(argc, argv);
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