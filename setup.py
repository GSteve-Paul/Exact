# To upload a package to PyPI, follow the instructions on https://packaging.python.org/en/latest/tutorials/packaging-projects

from pybind11.setup_helpers import Pybind11Extension
from setuptools import setup

__version__ = "2.0.0"

# The main interface is through Pybind11Extension.
# * You can add cxx_std=11/14/17, and then build_ext can be removed.
# * You can set include_pybind11=false to add the include directory yourself,
#   say from a submodule.
#
# Note:
#   Sort input source files if you glob sources to ensure bit-for-bit
#   reproducible builds (https://github.com/pybind/python_example/pull/53)

ext_modules = [
    Pybind11Extension(
        "exact",
        [
            "src/constraints/Constr.cpp",
            "src/constraints/ConstrExp.cpp",
            "src/constraints/ConstrSimple.cpp",
            "src/constraints/ConstrExpPools.cpp",
            "src/propagation/LpSolver.cpp",
            "src/Solver.cpp",
            "src/IntProg.cpp",
            "src/datastructures/SolverStructs.cpp",
            "src/Logger.cpp",
            "src/datastructures/IntSet.cpp",
            "src/parsing.cpp",
            "src/datastructures/Heuristic.cpp",
            "src/Stats.cpp",
            "src/Options.cpp",
            "src/auxiliary.cpp",
            "src/Optimization.cpp",
            "src/quit.cpp",
            "src/propagation/Propagator.cpp",
            "src/propagation/Equalities.cpp",
            "src/propagation/Implications.cpp",
            "src/used_licenses/licenses.cpp",
            "src/used_licenses/zib_apache.cpp",
            "src/used_licenses/roundingsat.cpp",
            "src/used_licenses/MIT.cpp",
            "src/used_licenses/boost.cpp",
            "src/used_licenses/EPL.cpp",
            "src/used_licenses/COPYING.cpp",
            "src/Exact.cpp"
        ],
        # FOR WINDOWS
        # include_dirs=['C:\\Program Files\\boost\\boost_1_85_0'],
        # extra_compile_args=["/O2","/std:c++20"],
        # define_macros=[("UNIXLIKE",0),("ANKERLMAPS",1)]
        # FOR LINUX / OSX
        extra_compile_args=["-O3","-std=c++20"],
        define_macros=[("UNIXLIKE",1),("ANKERLMAPS",1)]
    ),
]

setup(
    name="exact",
    version=__version__,
    author="Jo Devriendt",
    author_email="jo.devriendt@nonfictionsoftware.com",
    url="https://gitlab.com/JoD/exact",
    description="Python bindings for Exact",
    long_description="TODO",
    ext_modules=ext_modules,
    python_requires=">=3.7",
)
