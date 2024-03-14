#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/stl_bind.h>

#include "Exact.hpp"

namespace py = pybind11;
using namespace pybind11::literals;

PYBIND11_MODULE(exact, m) {
  m.doc() = "pybind11 Exact plugin";

  py::enum_<SolveState>(m, "SolveState")
      .value("UNSAT", SolveState::UNSAT)
      .value("SAT", SolveState::SAT)
      .value("INCONSISTENT", SolveState::INCONSISTENT)
      .value("TIMEOUT", SolveState::TIMEOUT)
      .value("INPROCESSED", SolveState::INPROCESSED)
      .export_values();

  py::class_<Exact>(m,"Exact")
      .def(py::init<const std::vector<std::pair<std::string, std::string>>&>(),
          "Constructor for the Exact solver",
           "options"_a = std::vector<std::pair<std::string, std::string>>{})
      .def("addVariable",
           py::overload_cast<const std::string&, int64_t, int64_t, const std::string&>(&Exact::addVariable),
           "Add a variable",
           "name"_a, "lower_bound"_a=0, "upper_bound"_a=1, "encoding"_a="log")
      .def("addVariable",
           py::overload_cast<const std::string&, const std::string&, const std::string&, const std::string&>(&Exact::addVariable),
           "Add a variable",
           "name"_a, "lower_bound"_a=0, "upper_bound"_a=1, "encoding"_a="log")
      .def("getVariables",
           &Exact::getVariables)
      .def("addConstraint",
           py::overload_cast<const std::vector<std::pair<int64_t, std::string>>&, bool, int64_t, bool, int64_t>(&Exact::addConstraint),
           "Add a linear constraint",
           "terms"_a, "use_lower_bound"_a=false, "lower_bound"_a=0, "use_upper_bound"_a=false, "upper_bound"_a=0)
      .def("addConstraint",
           py::overload_cast<const std::vector<std::pair<std::string, std::string>>&, bool, const std::string&, bool, const std::string&>(&Exact::addConstraint),
           "Add a linear constraint",
           "terms"_a, "use_lower_bound"_a=false, "lower_bound"_a=0, "use_upper_bound"_a=false, "upper_bound"_a=0)
      .def("setObjective",
           py::overload_cast<const std::vector<std::pair<int64_t,std::string>>&, bool, int64_t>(&Exact::setObjective),
           "Set a linear objective",
           "terms"_a, "minimize"_a=true, "offset"_a=0)
      .def("setObjective",
           py::overload_cast<const std::vector<std::pair<std::string,std::string>>&, bool, const std::string&>(&Exact::setObjective),
           "Set a linear objective",
           "terms"_a, "minimize"_a=true, "offset"_a=0)
      .def("runFull",
           &Exact::runFull,
           "Run solver until completion",
           "optimize"_a=true, "timeout"_a=0)
      .def("hasSolution",
           &Exact::hasSolution,
           "Return whether a solution has been found")
      .def("getObjectiveBounds",
           &Exact::getObjectiveBounds,
           "Return current objective bounds")
      .def("getObjectiveBounds_arb",
           &Exact::getObjectiveBounds_arb,
           "Return current objective bounds")
      .def("getLastSolutionFor",
           &Exact::getLastSolutionFor,
           "Return the values of the given variables in the last solution",
           "vars"_a)
      .def("getLastSolutionFor_arb",
           &Exact::getLastSolutionFor_arb,
           "Return the values of the given variables in the last solution",
           "vars"_a)
      ;
}
