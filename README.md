# Exact

Exact solves decision and optimization problems formulated as binary linear programs, also known as 0-1 integer linear programs or pseudo-Boolean formulas.

Exact is a fork of [RoundingSat](https://gitlab.com/miao_research/roundingsat) and improves upon its predecessor in reliability, performance and ease-of-use.
The name "Exact" reflects that the answers are fully sound, as approximate and floating-point calculations only occur in heuristic parts of the algorithm.
As such, Exact can soundly be used for verification and theorem proving, where its envisioned ability to emit machine-checkable certificates of optimality and unsatisfiability should prove useful.

## Features

- Native conflict analysis over binary linear constraints, constructing full-blown cutting planes proofs.
- Highly efficient watched propagation routines.
- Seamless use of arbitrary precision arithmetic.
- Hybrid linear (top-down) and core-guided (bottom-up) optimization.
- Optional integration with the SoPlex LP solver.
- Compiles on macOS.
- Under development: generation of certificates of optimality and unsatisfiability that can be automatically verified by [VeriPB](https://github.com/StephanGocht/VeriPB).

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
- Boost library (https://www.boost.org). 
  On a Debian/Ubuntu system, install with `sudo apt install libboost-all-dev`.
- Optionally: CoinUtils library (https://github.com/coin-or/CoinUtils) to parse MPS and LP file formats. 
  On a Debian/Ubuntu system, install with `sudo apt install coinor-libcoinutils-dev`.
- Optionally: SoPlex LP solver (see below)

## SoPlex

Exact supports an integration with the LP solver [SoPlex](https://soplex.zib.de) to improve its search routine.
For this, first [download](https://soplex.zib.de/download.php?fname=soplex-5.0.2.tgz) SoPlex 5.0.2 and place the downloaded file in the root directory of Exact.
Next, follow the above build process, but configure with the cmake option `-Dsoplex=ON`:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release -Dsoplex=ON ..
    make

The location of the SoPlex package can be configured with the cmake option `-Dsoplex_pkg=<location>`.

## Usage

Exact takes as input a binary linear program and outputs a(n optimal) solution or reports that none exists.
Either pipe the program

    cat test/instances/opb/opt/stein15.opb | build/Exact

or pass the file as a parameter

    build/Exact test/instances/opb/opt/stein15.opb

Exact supports five input formats:
- `.opb` pseudo-Boolean PBO (only linear objective and constraints)
- `.cnf` DIMACS Conjunctive Normal Form (CNF)
- `.wcnf` Weighted Conjunctive Normal Form (WCNF)
- `.mps` Mathematical Programming System (MPS) via the optional CoinUtils library
- `.lp` Linear Program (LP) via the optional CoinUtils library

By default, Exact decides on the format based on the filename extension, but this can be overridden with the `--format` option.

For a description of these input formats, see [here](InputFormats.md).

Use the flag `--help` to display a list of runtime parameters.

## Citations

Origin paper with a focus on cutting planes conflict analysis:  
**[EN18]** J. Elffers, J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*

Integration with SoPlex:  
**[DGN20]** J. Devriendt, A. Gleixner, J. Nordström. Learn to Relax: Integrating 0-1 Integer Linear Programming with Pseudo-Boolean Conflict-Driven Search. *CPAIOR 2020 / Constraints journal*

Watched propagation:  
**[D20]** J. Devriendt. Watched Propagation for 0-1 Integer Linear Constraints. *CP 2020*

Core-guided optimization:  
**[DGDNS21]** J. Devriendt, S. Gocht, E. Demirović, J. Nordström, P. J. Stuckey. Cutting to the Core of Pseudo-Boolean Optimization: Combining Core-Guided Search with Cutting Planes Reasoning. *AAAI 2021*
