/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2023 Jo Devriendt, Nonfiction Software

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

#include <csignal>
#include "ILP.hpp"
#include "quit.hpp"
#include "typedefs.hpp"

using namespace xct;

int main(int argc, char** argv) {

  // Global global;
  // ConstrExp32 ce32(global);

  // global.cePools.resize(6);

  // Ce32 reason = global.cePools.take32();

  // reason->addLhs(5, 1);
  // reason->addLhs(5, 2);
  // reason->addLhs(3, 3);
  // reason->addLhs(2, 4);
  // reason->addLhs(1, 5);
  // reason->addRhs(6); // reason = 5a+5b+3c+2d+e>=6


  // Ce32 confl = global.cePools.take32();

  // confl->addLhs(3, -2);
  // confl->addLhs(2, 1);
  // confl->addLhs(2, 4);
  // confl->addLhs(1, -5);

  // confl->addRhs(5);

  // // confl = 3~b+2a+2d+~e>=5

  // reason->toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;
  // confl->toStreamPure(std::cout);

  // IntMap<int> level;
  // level.resize(6, 0);
  // level[1] = INF;
  // level[-1] = INF;
  // level[2] = INF;
  // level[-2] = INF;
  // level[3] = INF;
  // level[-3] = INF;
  // level[4] = INF;
  // level[-4] = INF;
  // level[5] = INF;
  // level[-5] = INF;

  // level[-1] = 1;
  // level[-4] = 1;
  // level[5] = 2;
  // level[2] = 3;

  // // a=d=0, e=1, c=/ => prop b=1

  // std::vector<Lit> trail = {0, 0, 1, 1};
  // std::vector<int> pos = {0, 3, INF, 1, 2};

  // // std::vector<Lit> trail = {0, 0, 0, 1, 1};
  // // std::vector<int> pos = {0, 1, 2, 3, 4};

  // Lit asserting = 2;

  // std::cout << "\n" << std::endl;
  // std::cout << "slack confl: " << confl->getSlack(level) << std::endl;
  // std::cout << "slack reason: " << reason->getSlack(level) << std::endl;

  // // for (int i = 1; i < 6; i++) {
  // //   std::cout << "var is true: " << isTrue(level, i) << "\n" << std::endl;
  // //   std::cout << "var is false: " << isFalse(level, i) << "\n" << std::endl;
  // //   std::cout << "var is unknown: " << isUnknown(pos, i) << "\n" << std::endl;
  // // }

  // const int conflCoef = confl->getCoef(-asserting); // 3

  // std::cout << "confl coeff: " << conflCoef << std::endl;
  // // std::cout << "reason coeff: " << reasonCoef << std::endl;


  // // if (strcmp(argv[1], "mult") == 0) std::cout << "multiplied reason: " << std::endl;

  // // std::cout << argc << std::endl;

  // // for (int i = 0; i < argc; i++) {
  // //   std::cout << argv[i] << std::endl;
  // // }


  // const int reasonCoef = reason->getCoef(asserting); // 5
  // std::cout << "reason coeff: " << reasonCoef << "\n" << std::endl;

  // int mu = 1;
  // int nu = 1;
  // if (reasonCoef > conflCoef) {
  //   mu = aux::floordiv(reasonCoef, conflCoef); // 1
  // } else {
  //   nu = aux::ceildiv(conflCoef, reasonCoef); // 1
  // }

  // std::cout << "mu: " << mu << "\n" << std::endl;
  // std::cout << "nu: " << nu << "\n" << std::endl;

  // int reasonSlack = reason->getSlack(level); // rslack=3
  // std::cout << "reason slack: " << reasonSlack << "\n" << std::endl;
  
  // int conflSlack = confl->getSlack(level); // cslack=-5
  // std::cout << "confl slack: " << conflSlack << "\n" << std::endl;

  // int reasonDeg = reason->getDegree(); // rdeg=6
  // std::cout << "reason deg: " << reasonDeg << "\n" << std::endl;

  // // new_slack = nu*reasonslack + mu*conflictslack 
  // // weakenen = nu*reasondeg - mu*conflictcoef
  // // saturate = nu*rcoef - mu*ccoef

  // // rcoef > ccoef => rdeg > ccoef
  // // rcoef < ccoef => ccoef/rcoef*rdeg > ccoef

  // if (nu*(reasonSlack-reasonCoef)+mu*(conflCoef+conflSlack) < 0) { // 3 - 5 + (3 + -5) < -4
  //   std::cout << "going with mult and weaken" << std::endl;
  //   reason->multiply(nu);
  //   confl->multiply(mu);

  //   std::cout << "multiplied reason with nu and conflict with mu: " << std::endl;
  //   reason->toStreamPure(std::cout);
  //   std::cout << "\n" << std::endl;
  //   confl->toStreamPure(std::cout);
  //   std::cout << "\n" << std::endl;

  //   int amount = reasonDeg - confl->getCoef(-asserting);
  //   std::cout << "amount: " << amount << "\n" << std::endl;

  //   reason->weakenNonFalsified(level, amount); // r = 3a+3b+c+2d>= 3
  //   reason->saturate(false, false);
  //   std::cout << "weakened and saturated reason: " << std::endl;
  //   reason->toStreamPure(std::cout);
  //   std::cout << "\n" << std::endl;

  // } else {
  //   std::cout << "div options" << std::endl;
  //   if (strcmp(argv[1], "mult") == 0) reason->multiply(conflCoef);
  //   reason->toStreamPure(std::cout);
  //   std::cout << "\n" << std::endl;

  //   if (strcmp(argv[2], "rto") == 0) {

  //     reason->weakenDivideRoundOrdered(reasonCoef, level);

  //     reason->toStreamPure(std::cout);
  //     std::cout << "\n" << std::endl;

  //     reason->multiply(conflCoef);

  //     reason->toStreamPure(std::cout);
  //     std::cout << "\n" << std::endl;
  //   } else {
  //     int reasonSlack = reason->getSlack(level);
  //     std::cout << "reason slack+1: " << reasonSlack + 1 << "\n" << std::endl;
  //     std::cout << "reasonCoef / (reasonSlack + 1): " << reasonCoef / (reasonSlack + 1) << "\n" << std::endl;
  //     if (strcmp(argv[2], "slack+1") == 0 && reasonSlack > 0 && reasonCoef / (reasonSlack + 1) < conflCoef) {
  //       reason->weakenDivideRoundOrdered(reasonSlack + 1, level);
  //       std::cout << "weakened reason: " << std::endl;
  //       reason->toStreamPure(std::cout);
  //       std::cout << "\n" << std::endl;
  //       reason->multiply(aux::ceildiv(conflCoef, reason->getCoef(asserting)));
  //       std::cout << "multiplied reason: " << std::endl;
  //       reason->toStreamPure(std::cout);
  //       std::cout << "\n" << std::endl;
  //     } else {
  //       int gcd = strcmp(argv[1], "mult") == 0 ? conflCoef : aux::gcd(conflCoef, reasonCoef);
  //       std::cout << "gcd: " << gcd << "\n" << std::endl;
  //       const int minDiv = reasonCoef / gcd;
  //       std::cout << "minDiv: " << minDiv << "\n" << std::endl;
  //       int bestDiv = minDiv;
  //       if (bestDiv <= reasonSlack) {
  //         // quick heuristic search for small divisor larger than slack
  //         bestDiv = reasonCoef;
  //         int tmp;
  //         int pp;
  //         for (int p : {5, 3, 2}) {
  //           pp = 1;
  //           while ((gcd % p) == 0) {
  //             gcd /= p;
  //             tmp = reasonCoef / gcd;
  //             if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
  //             tmp = minDiv * gcd;
  //             if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
  //             pp *= p;
  //             tmp = reasonCoef / pp;
  //             if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
  //             tmp = minDiv * pp;
  //             if (tmp < bestDiv && tmp > reasonSlack) bestDiv = tmp;
  //           }
  //         }
  //       }
  //       std::cout << "bestDiv: " << bestDiv << "\n" << std::endl;
  //       const int mult = conflCoef / (reasonCoef / bestDiv);
  //       std::cout << "mult: " << mult << "\n" << std::endl;
  //       if (strcmp(argv[3], "cancel") == 0) {
  //         reason->weakenDivideRoundOrderedCanceling(bestDiv, level, pos, mult, *confl);
  //         reason->multiply(mult);
  //         // NOTE: since canceling unknowns are rounded up, the reason may have positive slack
  //       } else {
  //         std::cout << "reason: " << std::endl;
  //         reason->toStreamPure(std::cout);
  //         std::cout << "\n" << std::endl;
  //         reason->weakenDivideRoundOrdered(bestDiv, level);
  //         reason->multiply(mult);
  //         std::cout << "weakened reason: " << std::endl;
  //         reason->toStreamPure(std::cout);
  //         std::cout << "\n" << std::endl;
  //       }
  //     }
  //   }
  // }



  // // for (Var v : reason->vars) {
  // //   Lit ll = reason->getLit(v);
  // //   if (isFalse(level, ll)) {
  // //     actSet.add(v);
  // //   }
  // // }

  // int oldDegree = confl->getDegree();
  // // add reason to conflict
  // confl->addUp(reason); // 5a+4d+c+~e>= 5
  // // mindiv: 5a+5d+~e>=5

  // std::cout << "added reason to confl: " << std::endl;
  // confl->toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;

  // std::vector<Var>& varsToCheck = oldDegree <= confl->getDegree() ? reason->vars : confl->vars;
  // int largestCF = confl->getLargestCoef(varsToCheck);
  // if (largestCF > confl->getDegree()) {
  //   confl->saturate(varsToCheck, false, false);
  //   largestCF = static_cast<int>(confl->getDegree());
  // }

  // std::cout << "saturated confl: " << std::endl;
  // confl->toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;
  // // std::cout << "\n weaken first lit: " << std::endl;

  // // constr->weaken(1);

  // // constr->toStreamPure(std::cout);
  // // std::cout << "\n restore: " << std::endl;

  // // constr->addLhs(2, 1);
  // // constr->addRhs(2);

  // // constr->toStreamPure(std::cout);
  // // std::cout << "\n weaken superfluous: " << std::endl;

  // // // decide(1);

  // // constr->weakenSuperfluous(2, false, []([[maybe_unused]] Var v) { return true; });
  // // std::cout << "\n divide by 2 and round up: " << std::endl;

  // // constr->divideRoundUp(2);

  // // constr->toStreamPure(std::cout);
  // // std::cout << "\n" << std::endl;

  // // for (int i = 5; i > 0; i--) {
  // //   std::cout << i << " ";
  // // }
  // return 0;

  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if UNIXLIKE
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  ILP ilp;
  try {
    ilp.runInternal(argc, argv);
  } catch (const AsynchronousInterrupt& ai) {
    std::cout << "c " << ai.what() << std::endl;
    return quit::exit_INDETERMINATE(ilp);
  } catch (const UnsatEncounter& ue) {
    return quit::exit_SUCCESS(ilp);
  } catch (const std::invalid_argument& ia) {
    return quit::exit_ERROR(ia.what());
  } catch (const EarlyTermination& et) {
    return quit::exit_EARLY();
  }
  return quit::exit_SUCCESS(ilp);
}