/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 45

For each prime \(p \le N\), choose a residue class \(a_p \pmod p\).
Is it possible to do this in such a way that **every integer**
\(n\) with \(1 \le n \le N\) lies in **at least 10** of the chosen
residue classes?

Equivalently, can one select congruence classes
\(\{a_p \bmod p\}_{p \le N}\) so that for every \(n \le N\),
there are at least 10 primes \(p \le N\) with
\(n \equiv a_p \pmod p\)?

## Status
Open.

## Related
This problem is closely related to Green's Open Problem 44.

## Reference
- [Ben Green, *100 Open Problems*, Problem 45](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.45)
-/
