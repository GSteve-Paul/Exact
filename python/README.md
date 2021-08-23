# Exact

[Exact](https://gitlab.com/JoD/exact) solves decision and optimization problems formulated as binary linear programs, also known as 0-1 integer linear programs or pseudo-Boolean formulas.

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
- Python interface with assumption solving. Published as a [PyPI package](https://pypi.org/project/exact). (supporting only Linux for now)
- Under development: generation of certificates of optimality and unsatisfiability that can be automatically verified by [VeriPB](https://github.com/StephanGocht/VeriPB).

## Usage

**TODO: explain how to use this Python package**

## Build

after moving the .so and the headers to the folder `exact`, run

```
$ poetry build
$ poetry publish
```

## Citations

Origin paper with a focus on cutting planes conflict analysis:  
**[EN18]** J. Elffers, J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*

Integration with SoPlex:  
**[DGN20]** J. Devriendt, A. Gleixner, J. Nordström. Learn to Relax: Integrating 0-1 Integer Linear Programming with Pseudo-Boolean Conflict-Driven Search. *CPAIOR 2020 / Constraints journal*

Watched propagation:  
**[D20]** J. Devriendt. Watched Propagation for 0-1 Integer Linear Constraints. *CP 2020*

Core-guided optimization:  
**[DGDNS21]** J. Devriendt, S. Gocht, E. Demirović, J. Nordström, P. J. Stuckey. Cutting to the Core of Pseudo-Boolean Optimization: Combining Core-Guided Search with Cutting Planes Reasoning. *AAAI 2021*
