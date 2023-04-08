### 2023-03-22 
- commit: 8c77fcc4e28a88e27cc4cd9fe34701a76f822627 
- change: the meaning of the argument of `runFull(bool)` has been flipped: `False` now stops at satisfiability, while
  `True` keeps optimizing by adding objective bound constraints to improve the following solution. Additionally, 
  `runFull()` no longer adds objective bound constraints.
- rationale: it was very annoying to end up in an infinite loop or unexpected unsatisfiability when incorrectly setting 
  Exact's option to automatically add objective bound constraints. With this change, users can denote (and are forced
  to) whether they want to optimize or search for satisfiability with just one parameter. 

### 2023-04-08
- commit: 3f6db7a4acb38cdf7e0b362780f4f9305958120c
- changes:
- - add SolveState::TIMEOUT (3) to the Python interface.
- - add timeout parameter to propagated and pruneDomains from Python
  interface.
- - SolveState::TIMEOUT is now returned by runFull when timeout is
  detected to be exceeded. In particularly hard problems, timeouts may
  take a while to be detected (as we only check the outer loop). The
  search state is still valid after timeout is reached.
- - propagate and pruneDomains no longer throw an unsatEncounter exception when called on an unsatisfiable problem, but have a defined return value.
- rationale:
It is useful to have some form of recoverable timeout from the Python interface, even though it is not as finegrained as the non-recoverable timeout from the commandline.