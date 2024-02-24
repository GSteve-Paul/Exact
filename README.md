# Exact

[Exact](https://gitlab.com/JoD/exact) solves decision and optimization problems formulated as integer linear programs. Under the hood, it converts integer variables to binary (0-1) variables and applies highly efficient propagation routines and strong cutting-planes / pseudo-Boolean conflict analysis.

Exact is a fork of [RoundingSat](https://gitlab.com/MIAOresearch/roundingsat) and improves upon its predecessor in reliability, performance and ease-of-use.
The name "Exact" reflects that the answers are fully sound, as approximate and floating-point calculations only occur in heuristic parts of the algorithm.
As such, Exact can soundly be used for verification and theorem proving, where its envisioned ability to emit machine-checkable certificates of optimality and unsatisfiability should prove useful.


## Stay updated

Follow [@ExactSolver](https://twitter.com/ExactSolver) on Twitter and join the [reddit community](https://reddit.com/r/exact).


## Features

- **Native conflict analysis** over binary linear constraints, constructing full-blown cutting planes proofs.
- Highly efficient **watched propagation** routines.
- Seamless use of **arbitrary precision** arithmetic when needed.
- Hybrid linear (top-down) and **core-guided** (bottom-up) optimization.
- Optional integration with the **SoPlex LP solver**.
- Core solver also compiles on **macOS** and **Windows**.
- Under development: **Python** interface with assumption solving and reuse of solver state (Linux only for now).
- Under development: generation of **certificates** of optimality and unsatisfiability that can be automatically verified by [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB).


## Python interface

### PyPi package

The easiest way is to use an **x86_64** machine with **Linux** operating system. In that case, install this precompiled [PyPi package](https://pypi.org/project/exact), e.g., by running `pip3 install exact`.

### Compile your own Python package

To use the Exact Python interface with optimal binaries for your machine (and the option to include SoPlex in the binary), compile as a shared library and install it with your package manager (e.g., `pip`).

On Linux, [this script](https://gitlab.com/JoD/exact/-/blob/main/python/install_package.sh) should do the trick.
On other systems, something similar should work.
Make sure to have the Boost libraries installed (see dependencies).

### Documentation

The header file [`Exact.hpp`](https://gitlab.com/JoD/exact/-/blob/main/src/Exact.hpp) contains the C++ methods exposed to Python via [cppyy](https://cppyy.readthedocs.io/en/latest) as well as their description. This is probably the place to start to learn about Exact's Python usage.

Next, [`python/examples`](https://gitlab.com/JoD/exact/-/blob/main/python/examples) contains instructive, fully commented examples.
- [`python/examples/knapsack_classic.py`](https://gitlab.com/JoD/exact/-/blob/main/python/examples/knapsack_classic.py) showcases how to solve an integer classic knapsack problem with Exact's Python interface.
- [`python/examples/knapsack_implied.py`](https://gitlab.com/JoD/exact/-/blob/main/python/examples/knapsack_implied.py) elaborates on the first and showcases how to find the variable assignments implied by optimality, i.e., the variable assignments shared by all optimal solutions. A combination of the mechanics of assumption and solution invalidation allow to reuse the existing solver state (containing learned constraints) for optimal performance.
- [`python/examples/knapsack_propagate.py`](https://gitlab.com/JoD/exact/-/blob/main/python/examples/knapsack_propagate.py) elaborates on the second and showcases the builtin propagate method, which returns implied variable bounds under given assumptions.
- [`python/examples/ramsey.py`](https://gitlab.com/JoD/exact/-/blob/main/python/examples/knapsack_propagate.py) tries to compute the infamous [Ramsey numbers](https://en.wikipedia.org/wiki/Ramsey%27s_theorem).
- [`python/examples/graph_coloring/graph_coloring.py`](https://gitlab.com/JoD/exact/-/blob/main/python/examples/graph_coloring/graph_coloring.py) tries to find the chromatic number of a graph. If you can get Exact to prove the provided graph cannot be colored with 6 colors, contact @JoD ;)


## Command line usage

Exact takes as input an integer linear program and outputs a(n optimal) solution or reports that none exists.
Either pipe the program

    cat test/instances/opb/opt/stein15.opb | build/Exact

or pass the file as a parameter

    build/Exact test/instances/opb/opt/stein15.opb

Use the flag `--help` to display a list of runtime parameters.

Exact supports five input formats (described in more detail in [`InputFormats.md`](https://gitlab.com/JoD/exact/-/blob/main/InputFormats.md)):
- `.opb` pseudo-Boolean PBO (only linear objective and constraints)
- `.cnf` DIMACS Conjunctive Normal Form (CNF)
- `.wcnf` Weighted Conjunctive Normal Form (WCNF)
- `.mps` Mathematical Programming System (MPS) via the optional CoinUtils library
- `.lp` Linear Program (LP) via the optional CoinUtils library

Note that `.mps` and `.lp` allow rational variables, which are not supported by Exact.
Additionally, these formats permit floating point values, which may lead to [tricky](https://gitlab.com/JoD/exact/-/issues/11) [issues](https://gitlab.com/JoD/exact/-/issues/12).
Rewrite constraints with fractional values to integral ones by multiplying with the lowest common multiple of the denominators. 

By default, Exact decides on the format based on the filename extension, but this can be overridden with the `--format` option.


## Compilation

In the root directory of Exact:

    cd build
    cmake .. -DCMAKE_BUILD_TYPE=Release
    make

For a debug build:

    cd build_debug
    cmake .. -DCMAKE_BUILD_TYPE=Debug
    make

For more builds, similar build directories can be created.

For installing system-wide or to the `CMAKE_INSTALL_PREFIX` root, use `make install`.


## Dependencies

- A reasonably recent C++ compiler (GCC, Clang or MSVC should do)
- [Boost](https://www.boost.org) library.
  On a Debian/Ubuntu system, install with `sudo apt install libboost-dev`.
- Optionally: [CoinUtils](https://github.com/coin-or/CoinUtils) library to parse MPS and LP file formats.
  Use CMake option `-Dcoinutils=ON` after [installing the library](https://github.com/coin-or/CoinUtils#binaries).
- Optionally: [SoPlex](https://soplex.zib.de) LP solver (see below).


## SoPlex

Exact supports an integration with the LP solver [SoPlex](https://soplex.zib.de) to improve its search routine.
For this, checkout SoPlex from its [git repository](https://github.com/scipopt/soplex) as a submodule, compile it in some separate directory, and configure the right CMake options when compiling Exact.

By default, the following commands in Exact's root directory should work with a freshly checked out repository:
```
    git submodule init
    git submodule update

    mkdir soplex_build
    cd soplex_build
    cmake ../soplex -DBUILD_TESTING="0" -DSANITIZE_UNDEFINED="0" -DCMAKE_BUILD_TYPE="Release" -DBOOST="0" -DGMP="0" -DCMAKE_WINDOWS_EXPORT_ALL_SYMBOLS="0" -DZLIB="0"
    make -j 8

    cd ../build_debug
    cmake .. -DCMAKE_BUILD_TYPE="Release" -Dsoplex="ON"
    make -j 8
```
The CMake options `soplex_src` and `soplex_build` allow to look for SoPlex in a different location.


## License

Exact is licensed under the [AGPLv3](https://www.gnu.org/licenses/agpl-3.0.en.html). If this would hinder your intended usage, please contact @JoD.


## Benchmarks

The current set of benchmarks which is used to assess performance is available [here](https://gitlab.com/JoD/exact-benchmarks).


## Citations

If you use Exact, please **star and cite this repository** and cite the RoundingSat origin paper (which focuses on cutting planes conflict analysis):  
**[EN18]** J. Elffers, J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*

Please cite any of the foloowing papers if they are relevant.

Integration with SoPlex:  
**[DGN20]** J. Devriendt, A. Gleixner, J. Nordström. Learn to Relax: Integrating 0-1 Integer Linear Programming with Pseudo-Boolean Conflict-Driven Search. *CPAIOR 2020 / Constraints journal*

Watched propagation:  
**[D20]** J. Devriendt. Watched Propagation for 0-1 Integer Linear Constraints. *CP 2020*

Core-guided optimization:  
**[DGDNS21]** J. Devriendt, S. Gocht, E. Demirović, J. Nordström, P. J. Stuckey. Cutting to the Core of Pseudo-Boolean Optimization: Combining Core-Guided Search with Cutting Planes Reasoning. *AAAI 2021*
