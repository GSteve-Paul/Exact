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
#include "typedefs.hpp"

using namespace xct;

int main(int argc, char** argv) {
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