# Thesis Orestis Lomis

This is the main branch of the work during the thesis of Orestis Lomis. You can find the specific work done in different branches. This branch mostly exist to have a stable version that new work can start of and to guide people to the correct branches if necessary.

## Branches

Throughout the thesis many different branches were made to test out parts of the solver in isolation. The changes to the code can usually be found at src/constraints/ConstrExp.hpp unless stated otherwise.

### Strength Analysis

- strength-analysis: This branch focuses on the strength analysis. This code is not separate from the solver code, but is in this repository as part of the thesis. The code can be found at python/strength

### Exact Options

Most of the options can just be turned on or off in the main branch of Exact, so no separate branch was made to test out all the options. The options that were introduced separately are in the branches:

- full-weakening
- no-weaken-superfluous
- no-weaken-non-implied

### Multiply Weaken

- MWIndirect: This branch implements the multiply weaken algorithm using indirect weakening.
- MWDirect: This branch implements the multiply weaken algorithm using direct weakening
- MWCompare: This branch implements the multiply weaken algorithm. It learns a constraint through division and using both MW variants and learns the best one using the DGS heuristic.

### MIR

- MIR: This branch implements the 'weakenMIR' algorithm which is the MIR equivalent of 'weakenDivide'. It uses MIR as the reduction method.
- DivisionvsMIRCut: This branch uses the default division algorithm throughout, but reduces the reason using both a division and a MIR cut. It tracks the performance of both compared to each other.
- MIRvsDivisionCut: This branch uses the MIR algorithm throughout, but reduces the reason using both a division and a MIR cut. It tracks the performance of both compared to each other.
- MIRvsDivisionAlgo: This branch does conflict analysis using both the MIR and division algorithm separately and compares the two.

### Miscelaneous

Some aspects were briefly tested, but didn't make it into the thesis:

- weaken-superfluous-sweeping: This branch was made to see if superfluous weakening couldn't be improved through a better weakening order. Initial results showed there was not much of a difference and we didn't look further into it after realising superfluous weakening didn't have a big impact to begin with.
- no-actset: Exact uses a VSIDS like heuristic called the actset. MW doesn't use this heuristic, but this was only by accident at the beginning. After adding the actset heuristic to MW it performed worse however so we tested it out. On the main branch of Exact it does seem to provide much better results however. This is still worth looking into, but there wasn't enough time in the thesis.

## Results
