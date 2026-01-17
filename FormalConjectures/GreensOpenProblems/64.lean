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
# Ben Green's Open Problem 64

*Reference:* [Ben Green's Open Problem 64](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 64)
-/

namespace Green64

/--
Do there exist infinitely many primes $p$ for which $p - 2$ has an odd number of prime factors
(counted with multiplicity)?

The same question may be asked with $p - 1$ (and this is probably more natural), but with $p - 2$
the question is a weak form of the twin prime conjecture. The set of integers $S$ with an odd
number of prime factors has density $\frac{1}{2}$, so one is 'only' asking for infinitely many
primes in a set $(S + 1)$ of density $\frac{1}{2}$.
-/
@[category research open, AMS 11]
theorem green_64 :
    answer(sorry) ↔ {p : ℕ | p.Prime ∧ Odd (Nat.primeFactorsList (p - 2)).length}.Infinite := by
  sorry

end Green64
