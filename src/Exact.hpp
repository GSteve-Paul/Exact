/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include <string>

int main_python();

// addVariable() ?
// bool addObjective();
// getObjective();
// bool addConstraint();
// getConstraints();
// bool getUnits();
// SOLVERESULT solve(assumptions);
// getBest();

/* exit_SUCCESS:
 *
- attachConstraint
- learnConstraint
- addConstraint
- addConstraintChecked
- ILP::normalize
- addLowerBound
- handleNewSolution x 2
- optimize (UNSAT and SAT)
 *
 */

/*
 * - attachConstraint
- learnConstraint
- addConstraint
- addConstraintChecked
- ILP::normalize
- addLowerBound
- handleNewSolution x 2
- optimize (UNSAT and SAT)

attachConstraint

- learnConstraint
- - probe
- - - detectAtMostOne
- - - - runAtMostOneDetection
- - - - - inProcess
- - - - - - presolve
- - - - - - - solve
- - - - - - solve
- - - probeRestart
- - - - solve
- - extractCore
- - - solve
- - reduceDB
- - - solve
- - solve
- - detectAtMostOne
- - - runAtMostOneDetection
- - - - inProcess
- - addFilteredCuts
- - - LP::inProcess
- - - - inProcess
- - checkFeasiblity x2
- - - runPropagation() - done
- - - LP::inProcess



- AddUnitConstraint
- - harden
- - - handleNewSolution
- - - addLowerBound
 */
