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

#pragma once

#include "../datastructures/IntMap.hpp"
#include "Propagator.hpp"

namespace xct {

class Solver;

class Implications : public Propagator {
  IntMap<unordered_set<Lit>> implieds;
  long long implInMem = 0;

 public:
  Implications(Solver& s) : Propagator(s) {}
  void setNbVars(int n);

  void addImplied(Lit a, Lit b);
  void removeImplied(Lit a);
  const unordered_set<Lit>& getImplieds(Lit a) const;
  bool hasImplieds(Lit a) const;
  long long nImpliedsInMemory() const;

  State propagate();
};

}  // namespace xct