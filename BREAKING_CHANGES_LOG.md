# 2023-03-22 
- commit: 8c77fcc4e28a88e27cc4cd9fe34701a76f822627 
- change: the meaning of the argument of `runFull(bool)` has been flipped: `False` now stops at satisfiability, while
  `True` keeps optimizing by adding objective bound constraints to improve the following solution. Additionally, 
  `runFull()` no longer adds objective bound constraints.
- rationale: it was very annoying to end up in an infinite loop or unexpected unsatisfiability when incorrectly setting 
  Exact's option to automatically add objective bound constraints. With this change, users can denote (and are forced
  to) whether they want to optimize or search for satisfiability with just one parameter. 
