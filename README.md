# Exact

[Exact](https://gitlab.com/JoD/exact) solves decision and optimization problems formulated as integer linear programs. Under the hood, it converts integer variables to binary (0-1) variables and applies highly efficient propagation routines and strong cutting-planes / pseudo-Boolean conflict analysis.

Exact is a fork of [RoundingSat](https://gitlab.com/miao_research/roundingsat) and improves upon its predecessor in reliability, performance and ease-of-use.
The name "Exact" reflects that the answers are fully sound, as approximate and floating-point calculations only occur in heuristic parts of the algorithm.
As such, Exact can soundly be used for verification and theorem proving, where its envisioned ability to emit machine-checkable certificates of optimality and unsatisfiability should prove useful.

## Stay updated

Follow [@ExactSolver](https://twitter.com/ExactSolver) on Twitter.

## Features

- **Native conflict analysis** over binary linear constraints, constructing full-blown cutting planes proofs.
- Highly efficient **watched propagation** routines.
- Seamless use of **arbitrary precision** arithmetic when needed.
- Hybrid linear (top-down) and **core-guided** (bottom-up) optimization.
- Optional integration with the **SoPlex LP solver**.
- Compiles on **macOS**.
- Under development: **Python** interface with assumption solving and reuse of solver state.
- Under development: generation of **certificates** of optimality and unsatisfiability that can be automatically verified by [VeriPB](https://github.com/StephanGocht/VeriPB).

## Python interface

Either compile a shared library locally or use the published [PyPI package](https://pypi.org/project/exact) (Linux only for now) via the `pip` or `poetry` package managers.

The header file [`Exact.hpp`](https://gitlab.com/JoD/exact/-/blob/master/src/Exact.hpp) contains the C++ methods exposed to Python via [cppyy](https://cppyy.readthedocs.io/en/latest) as well as their description. This is probably the place to start to learn about Exact's Python usage.

Next, [`python/examples`](https://gitlab.com/JoD/exact/-/blob/master/python/examples) contains instructive, fully commented examples.
- [`python/examples/knapsack_classic.py`](https://gitlab.com/JoD/exact/-/blob/master/python/examples/knapsack_classic.py) showcases how to solve an integer classic knapsack problem with Exact's Python interface.
- [`python/examples/knapsack_implied.py`](https://gitlab.com/JoD/exact/-/blob/master/python/examples/knapsack_implied.py) elaborates on the first and showcases how to find the variable assignments implied by optimality, i.e., the variable assignments shared by all optimal solutions. A combination of the mechanics of assumption and solution invalidation allow to reuse the existing solver state (containing learned constraints) for optimal performance.
- [`python/examples/knapsack_propagate.py`](https://gitlab.com/JoD/exact/-/blob/master/python/examples/knapsack_propagate.py) elaborates on the second and showcases the builtin propagate method, which returns implied variable bounds under given assumptions.

## File-based usage

Exact takes as input an integer linear program and outputs a(n optimal) solution or reports that none exists.
Either pipe the program

    cat test/instances/opb/opt/stein15.opb | build/Exact

or pass the file as a parameter

    build/Exact test/instances/opb/opt/stein15.opb

Use the flag `--help` to display a list of runtime parameters.

Exact supports five input formats (described in more detail in [`InputFormats.md`](https://gitlab.com/JoD/exact/-/blob/master/InputFormats.md)):
- `.opb` pseudo-Boolean PBO (only linear objective and constraints)
- `.cnf` DIMACS Conjunctive Normal Form (CNF)
- `.wcnf` Weighted Conjunctive Normal Form (WCNF)
- `.mps` Mathematical Programming System (MPS) via the optional CoinUtils library
- `.lp` Linear Program (LP) via the optional CoinUtils library

By default, Exact decides on the format based on the filename extension, but this can be overridden with the `--format` option.

## Compilation

In the root directory of Exact:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..
    make

For a debug build:

    cd build_debug
    cmake -DCMAKE_BUILD_TYPE=Debug ..
    make

For more builds, similar build directories can be created.

For installing system-wide or to the `CMAKE_INSTALL_PREFIX` root, use `make install`.

## Dependencies

- C++17 (i.e., a reasonably recent C++ compiler)
- [Boost](https://www.boost.org) library.
  On a Debian/Ubuntu system, install with `sudo apt install libboost-all-dev`.
- Optionally: [CoinUtils](https://github.com/coin-or/CoinUtils) library to parse MPS and LP file formats.
  On a Debian/Ubuntu system, install with `sudo apt install coinor-libcoinutils-dev`.
- Optionally: [SoPlex](https://soplex.zib.de) LP solver (see below)

## SoPlex

Exact supports an integration with the LP solver [SoPlex](https://soplex.zib.de) to improve its search routine.
For this, first [download](https://soplex.zib.de/download.php?fname=soplex-6.0.0.tgz) SoPlex 6.0.0 and place the downloaded file in the root directory of Exact.
Next, follow the above build process, but configure with the cmake option `-Dsoplex=ON`:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release -Dsoplex=ON ..
    make

The location of the SoPlex package can be configured with the cmake option `-Dsoplex_pkg=<location>`.

## License

Exact is licensed under the [AGPLv3](https://www.gnu.org/licenses/agpl-3.0.en.html). If this would hinder your intended usage, please get in touch via jodevriendt.com/contact.

## Citations

Origin paper with a focus on cutting planes conflict analysis:  
**[EN18]** J. Elffers, J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*

Integration with SoPlex:  
**[DGN20]** J. Devriendt, A. Gleixner, J. Nordström. Learn to Relax: Integrating 0-1 Integer Linear Programming with Pseudo-Boolean Conflict-Driven Search. *CPAIOR 2020 / Constraints journal*

Watched propagation:  
**[D20]** J. Devriendt. Watched Propagation for 0-1 Integer Linear Constraints. *CP 2020*

Core-guided optimization:  
**[DGDNS21]** J. Devriendt, S. Gocht, E. Demirović, J. Nordström, P. J. Stuckey. Cutting to the Core of Pseudo-Boolean Optimization: Combining Core-Guided Search with Cutting Planes Reasoning. *AAAI 2021*
