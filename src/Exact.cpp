/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2024 Jo Devriendt, Nonfiction Software

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

#include "Exact.hpp"
#include <pybind11/stl.h>
#include <pybind11/stl_bind.h>
#include <csignal>
#include <fstream>
#include <iomanip>
#include <sstream>
#include "Exact.hpp"
#include "parsing.hpp"

namespace py = pybind11;
using namespace pybind11::literals;

using namespace xct;

/**
 * Below cpp_int to Python int conversion courtesy of tnt:
 * https://stackoverflow.com/questions/54738011/pybind11-boostmultiprecisioncpp-int-to-python
 */
namespace pybind11 {
namespace detail {
template <>
struct type_caster<bigint> {
  /**
   * This macro establishes the name 'bigint' in function signatures and declares a local variable 'value' of type
   * bigint
   */
  PYBIND11_TYPE_CASTER(bigint, _("bigint"));

  /**
   * Conversion part 1 (Python->C++): convert a PyObject into a bigint instance or return false upon failure. The
   * second argument indicates whether implicit conversions should be applied.
   */
  bool load(handle src, bool) {
    // Convert into base 16 string (PyNumber_ToBase prepend '0x')
    PyObject* tmp = PyNumber_ToBase(src.ptr(), 16);
    if (!tmp) return false;

    std::string s = py::cast<std::string>(tmp);
    value = bigint{s};
    // explicit cast from string to bigint don't need a base here because `PyNumber_ToBase` already prepended '0x'
    Py_DECREF(tmp);

    // Ensure return code was OK (to avoid out-of-range errors etc)
    return !PyErr_Occurred();
  }

  /**
   * Conversion part 2 (C++ -> Python): convert an bigint instance into a Python object. The second and third arguments
   * are used to indicate the return value policy and parent object (for ``return_value_policy::reference_internal``)
   * and are generally ignored by implicit casters.
   */
  static handle cast(const bigint& src, return_value_policy, handle) {
    // Convert bigint to base 16 string
    std::ostringstream oss;
    oss << std::hex << src;
    return PyLong_FromString(oss.str().c_str(), nullptr, 16);
  }
};
}  // namespace detail
}  // namespace pybind11

IntVar* Exact::getVariable(const std::string& name) const {
  IntVar* res = ilp.getVarFor(name);
  if (!res) throw InvalidArgument("No variable " + name + " found.");
  return res;
}

std::vector<IntVar*> Exact::getVars(const std::vector<std::string>& names) const {
  return aux::comprehension(names, [&](const std::string& name) { return getVariable(name); });
}

// TODO: reduce below code duplication using templates?

bigint getCoef(int64_t c) { return static_cast<bigint>(c); }
bigint getCoef(const std::string& c) { return bigint(c); }

std::vector<bigint> getCoefs(const std::vector<int64_t>& cs) {
  return aux::comprehension(cs, [](int64_t x) { return getCoef(x); });
}
std::vector<bigint> getCoefs(const std::vector<std::string>& cs) {
  return aux::comprehension(cs, [](const std::string& x) { return getCoef(x); });
}

Options getOptions(const std::vector<std::pair<std::string, std::string>>& options) {
  Options opts;
  for (auto pr : options) {
    opts.parseOption(pr.first, pr.second);
  }
  return opts;
}

Exact::Exact(const std::vector<std::pair<std::string, std::string>>& options) : ilp(getOptions(options), true) {
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif
}

void Exact::addVariable(const std::string& name, const bigint& lb, const bigint& ub, const std::string& encoding) {
  if (ilp.getVarFor(name)) throw InvalidArgument("Variable " + name + " already exists.");
  if (encoding != "" && encoding != "order" && encoding != "log" && encoding != "onehot") {
    throw InvalidArgument("Unknown encoding " + encoding +
                          ". Should be \"log\", \"order\" or \"onehot\", or left unspecified.");
  }
  ilp.addVar(name, lb, ub, encoding == "" ? Encoding::LOG : opt2enc(encoding));
}

std::vector<std::string> Exact::getVariables() const {
  return aux::comprehension(ilp.getVariables(), [](IntVar* iv) { return iv->getName(); });
}

void Exact::addConstraint(const std::vector<std::pair<bigint, std::string>>& terms, bool useLB, const bigint& lb,
                          bool useUB, const bigint& ub) {
  if (terms.size() > 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, aux::option(useLB, lb), aux::option(useUB, ub)};
  ic.lhs.resize(terms.size());
  for (const auto& t : terms) {
    ic.lhs.push_back({t.first, getVariable(t.second)});
  }
  ilp.addConstraint(ic);
}

void Exact::addReification(const std::string& head, bool sign, const std::vector<std::pair<bigint, std::string>>& terms,
                           const bigint& lb) {
  if (terms.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.reserve(terms.size());
  for (const auto& t : terms) {
    ic.lhs.push_back({t.first, getVariable(t.second)});
  }
  ilp.addReification(getVariable(head), sign, ic);
}

void Exact::addRightReification(const std::string& head, bool sign,
                                const std::vector<std::pair<bigint, std::string>>& terms, const bigint& lb) {
  if (terms.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.reserve(terms.size());
  for (const auto& t : terms) {
    ic.lhs.push_back({t.first, getVariable(t.second)});
  }
  ilp.addRightReification(getVariable(head), sign, ic);
}

void Exact::addLeftReification(const std::string& head, bool sign,
                               const std::vector<std::pair<bigint, std::string>>& terms, const bigint& lb) {
  if (terms.size() >= 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");

  IntConstraint ic = {{}, bigint(lb)};
  ic.lhs.reserve(terms.size());
  for (const auto& t : terms) {
    ic.lhs.push_back({t.first, getVariable(t.second)});
  }
  ilp.addLeftReification(getVariable(head), sign, ic);
}

void Exact::fix(const std::string& var, const bigint& val) { ilp.fix(getVariable(var), val); }

void Exact::setAssumptions(const std::vector<std::pair<std::string, bigint>>& varvals) {
  ilp.setAssumptions(getVars(varvals));
}
void Exact::setAssumptions(const std::vector<std::pair<std::string, std::vector<bigint>>>& varvals) {
  ilp.setAssumptions(getVars(varvals));
}

void Exact::clearAssumptions() { ilp.clearAssumptions(); }
void Exact::clearAssumptions(const std::vector<std::string>& vars) { ilp.clearAssumptions(getVars(vars)); }

bool Exact::hasAssumption(const std::string& var) const { return ilp.hasAssumption(getVariable(var)); }

std::vector<py::int_> Exact::getAssumption(const std::string& var) const {
  return aux::comprehension(ilp.getAssumption(getVariable(var)),
                            [](const bigint& i) -> py::int_ { return py::cast(i); });
}

void Exact::setSolutionHints(const std::vector<std::pair<std::string, bigint>>& hints) {
  ilp.setSolutionHints(getVars(hints));
}

void Exact::clearSolutionHints(const std::vector<std::string>& vars) { ilp.clearSolutionHints(getVars(vars)); }

void Exact::boundObjByLastSol() { ilp.getOptim()->boundObjByLastSol(); }
void Exact::invalidateLastSol() { ilp.invalidateLastSol(); }
void Exact::invalidateLastSol(const std::vector<std::string>& vars) { ilp.invalidateLastSol(getVars(vars)); }

void Exact::printVariables() const { ilp.printVars(std::cout); }
void Exact::printInput() const { ilp.printInput(std::cout); }
void Exact::printFormula() { ilp.printFormula(std::cout); }

void Exact::setObjective(const std::vector<std::pair<bigint, std::string>>& terms, bool minimize,
                         const bigint& offset) {
  if (terms.size() > 1e9) throw InvalidArgument("Objective has more than 1e9 terms.");

  std::vector<IntTerm> iterms;
  iterms.reserve(terms.size());
  for (const auto& t : terms) {
    iterms.push_back({t.first, getVariable(t.second)});
  }
  ilp.setObjective(iterms, minimize, offset);
}

std::string Exact::runOnce(double timeout) {
  if (timeout != 0) ilp.global.stats.runStartTime = std::chrono::steady_clock::now();
  SolveState res = ilp.getOptim()->run(false, timeout);
  if (res == SolveState::INCONSISTENT) return "PAUSED";
  return (std::stringstream() << res).str();
}

std::string Exact::runFull(bool optimize, double timeout) {
  if (timeout != 0) ilp.global.stats.runStartTime = std::chrono::steady_clock::now();
  ilp.getSolver().printHeader();
  return (std::stringstream() << ilp.getOptim()->runFull(optimize, timeout)).str();
}

std::pair<py::int_, py::int_> Exact::getObjectiveBounds() const {
  return {py::cast(ilp.getLowerBound()), py::cast(ilp.getUpperBound())};
}

bool Exact::hasSolution() const { return ilp.getSolver().foundSolution(); }

std::vector<py::int_> Exact::getLastSolutionFor(const std::vector<std::string>& vars) const {
  if (!hasSolution()) throw InvalidArgument("No solution can be returned if no solution has been found.");
  return aux::comprehension(ilp.getLastSolutionFor(getVars(vars)),
                            [](const bigint& i) -> py::int_ { return py::cast(i); });
}

std::vector<std::string> Exact::getLastCore() {
  Core core = ilp.getLastCore();
  if (core) {
    return aux::comprehension(*core, [](IntVar* iv) { return iv->getName(); });
  } else {
    return {};
  }
}

std::vector<std::pair<py::int_, py::int_>> Exact::propagate(const std::vector<std::string>& vars, double timeout) {
  return aux::comprehension(ilp.propagate(getVars(vars), true, {true, timeout}),
                            [](const std::pair<bigint, bigint>& x) -> std::pair<py::int_, py::int_> {
                              return std::pair<py::int_, py::int_>{py::cast(x.first), py::cast(x.second)};
                            });
}

std::vector<std::vector<py::int_>> Exact::pruneDomains(const std::vector<std::string>& vars, double timeout) {
  return aux::comprehension(ilp.pruneDomains(getVars(vars), true, {true, timeout}),
                            [](const std::vector<bigint>& x) -> std::vector<py::int_> {
                              return aux::comprehension(x, [](const bigint& y) -> py::int_ { return py::cast(y); });
                            });
}

int64_t Exact::count(const std::vector<std::string>& vars, double timeout) {
  return ilp.count(getVars(vars), true, {true, timeout}).second;
}

std::vector<std::pair<std::string, double>> Exact::getStats() {
  ilp.global.stats.setDerivedStats(static_cast<StatNum>(ilp.getLowerBound()),
                                   static_cast<StatNum>(ilp.getUpperBound()));
  return aux::comprehension(ilp.global.stats.statsToDisplay, [](Stat* s) {
    return std::pair<std::string, double>{s->name, static_cast<double>(s->z)};
  });
}

PYBIND11_MODULE(exact, m) {
  m.doc() = "pybind11 Exact plugin";
  py::class_<Exact>(m, "Exact")

      .def(py::init<const std::vector<std::pair<std::string, std::string>>&>(), "Constructor for the Exact solver",
           "options"_a = std::vector<std::pair<std::string, std::string>>{})

      .def("addVariable", &Exact::addVariable, "Add a variable", "name"_a, "lower_bound"_a = 0, "upper_bound"_a = 1,
           "encoding"_a = "log")

      .def("getVariables", &Exact::getVariables)

      .def("addConstraint", &Exact::addConstraint, "Add a linear constraint", "terms"_a, "use_lower_bound"_a = false,
           "lower_bound"_a = 0, "use_upper_bound"_a = false, "upper_bound"_a = 0)

      .def("addReification", &Exact::addReification, "Add a reification of a linear constraint", "head"_a, "sign"_a,
           "terms"_a, "lower_bound"_a)

      .def("addLeftReification", &Exact::addLeftReification, "Add a left reification of a linear constraint", "head"_a,
           "sign"_a, "terms"_a, "lower_bound"_a)

      .def("addRightReification", &Exact::addRightReification, "Add a right reification of a linear constraint",
           "head"_a, "sign"_a, "terms"_a, "lower_bound"_a)

      .def("fix", &Exact::fix)

      .def("setAssumptions",
           py::overload_cast<const std::vector<std::pair<std::string, bigint>>&>(&Exact::setAssumptions),
           "Assume a given value for given variables", "varvals"_a)
      .def("setAssumptions",
           py::overload_cast<const std::vector<std::pair<std::string, std::vector<bigint>>>&>(&Exact::setAssumptions),
           "Assume a set of allowed values for given variables", "varvals"_a)

      .def("clearAssumptions", py::overload_cast<>(&Exact::clearAssumptions), "Clear any previous assumptions")
      .def("clearAssumptions", py::overload_cast<const std::vector<std::string>&>(&Exact::clearAssumptions),
           "Clear any previous assumptions over the given variables", "vars"_a)

      .def("hasAssumption", &Exact::hasAssumption, "Check whether a given variable has assumptions", "var"_a)

      .def("getAssumption", &Exact::getAssumption, "Check which assumptions a given variable has", "var"_a)

      .def("setSolutionHints", &Exact::setSolutionHints, "Set solution hints", "hints"_a)

      .def("clearSolutionHints", &Exact::clearSolutionHints, "Clear any solution hints")

      .def("setObjective", &Exact::setObjective, "Set a linear objective", "terms"_a, "minimize"_a = true,
           "offset"_a = 0)

      .def("runFull", &Exact::runFull, "Run solver until completion", "optimize"_a = true, "timeout"_a = 0)

      .def("runOnce", &Exact::runOnce, "Run solver until some solve state is reached", "timeout"_a = 0)

      .def("hasSolution", &Exact::hasSolution, "Return whether a solution has been found")

      .def("getLastSolutionFor", &Exact::getLastSolutionFor,
           "Return the values of the given variables in the last solution", "vars"_a)

      .def("getLastCore", &Exact::getLastCore, "Return the last assumption-invalidating core")

      .def("boundObjByLastSol", &Exact::boundObjByLastSol, "Bound the objective by the last found solution")

      .def("invalidateLastSol", py::overload_cast<>(&Exact::invalidateLastSol),
           "Add a solution-invalidating constraint for the last found solution")
      .def("invalidateLastSol", py::overload_cast<const std::vector<std::string>&>(&Exact::invalidateLastSol),
           "Add a solution-invalidating constraint for the last found solution projected to the given variables")

      .def("getObjectiveBounds", &Exact::getObjectiveBounds, "Return current objective bounds")

      .def("propagate", &Exact::propagate, "Find implied lower and upper bound for given variables", "vars"_a,
           "timeout"_a = 0)

      .def("pruneDomains", &Exact::pruneDomains, "Find smallest possible domains for given variables", "vars"_a,
           "timeout"_a = 0)

      .def("count", &Exact::count, "Count number of different solutions over given variables", "vars"_a,
           "timeout"_a = 0)

      .def("printVariables", &Exact::printVariables, "Print variables given to Exact")
      .def("printInput", &Exact::printInput, "Print objective and constraints given to Exact")
      .def("printFormula", &Exact::printFormula, "Print Exact's internal formula")
      .def("getStats", &Exact::getStats, "Get Exact's internal statistics")

      ;
}
