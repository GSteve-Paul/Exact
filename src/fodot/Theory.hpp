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

#pragma once
#include "Expression.hpp"
#include "Fodot.hpp"

namespace xct {
class ILP;
}

namespace fodot {

const char BUILTINPRE = '[';
const char BUILTINPOST = ']';
std::string toBuiltin(const std::string& s);
std::string fromBuiltin(const std::string& s);

class Vocabulary {  // TODO: merge with theory?
  friend std::ostream& operator<<(std::ostream& o, const Vocabulary& v);

  std::unordered_map<std::string, std::unique_ptr<Functor>> name2functor;  // take arity into account for unicity?

  void addBuiltins();

 public:
  Vocabulary();
  void parseCsv(const std::string& filename);
  Functor* createFunctor(const std::string& name, const std::vector<Type>& types, const std::vector<DomEl>& range);
  Functor* createFunctor(const std::string& name, const std::vector<Type>& types,
                         const Functor& range);  // functor with set functor as range
  Functor* createBoolean(const std::string& name, const std::vector<Type>& types);
  Functor* createType(const std::string& name, const std::vector<DomEl>& inter);
  Functor* createInterpreted(const std::string& name, const std::vector<Tup>& inter, const DomEl& otherwise);
  std::vector<Functor*> createConstructed(const std::string& type, const std::string& func,
                                          const std::vector<std::pair<std::string, Functor*>>& attributes);
  Functor* createBuiltin(const std::string& repr, const std::vector<DomEl>& range);
  Functor* createTseitin(const std::string& repr);

  bool hasFunctor(const std::string& name);
  Functor* getFunctor(const std::string& name);

  void addTo(xct::ILP& ilp);
  void readModel(xct::ILP& ilp);
};
std::ostream& operator<<(std::ostream& o, const Vocabulary& v);

class Theory {
 public:
  Vocabulary voc;
  std::vector<Term> constraints;
  Term objective;

  void addTo(xct::ILP& ilp);

  void addMijnCollega();  // TODO: tmp
};
std::ostream& operator<<(std::ostream& o, const Theory& theo);

}  // namespace fodot
