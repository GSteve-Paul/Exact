from pybind11.setup_helpers import Pybind11Extension, build_ext, ParallelCompile, naive_recompile
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
        extra_compile_args=["-O3"],
        # Example: passing in the version to the compiled code
        # define_macros=[("VERSION_INFO", __version__)],
    ),
]

# Optional multithreaded build
ParallelCompile("NPY_NUM_BUILD_JOBS", default=6, needs_recompile=naive_recompile).install()

setup(
    name="exact",
    version=__version__,
    author="Jo Devriendt",
    author_email="jo.devriendt@nonfictionsoftware.com",
    url="https://gitlab.com/JoD/exact",
    description="Python bindings for Exact",
    long_description="TODO",
    ext_modules=ext_modules,
    # extras_require={"test": "pytest"},
    # Currently, build_ext only provides an optional "highest supported C++
    # level" feature, but in the future it may provide more features.
    cmdclass={"build_ext": build_ext},
    python_requires=">=3.7",
)
