/-
Copyright 2026 The Formal Conjectures Authors.

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
import FormalConjecturesUtil

/-!
# Polynomial-time computability of factoring

This file formalizes the open problem of whether natural number / integer factorization can be computed in
polynomial time on a deterministic classical Turing machine.

More precisely, it formalizes the following statement:
Can the prime factorization of a natural number be computed in polynomial time
(on a deterministic classical Turing machine)?

*References:*
- [Wikipedia: List of unsolved problems in computer science](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science)
- [Wikipedia: Integer factorization](https://en.wikipedia.org/wiki/Integer_factorization)

-/

namespace PolyTime

open ComplexityTheory


/--
**The integer factorization problem**: Can the prime factorization of a positive integer
be computed in polynomial time?

We state the problem by asking if `Nat.primeFactorsList` is polynomial-time computable
(assuming typical encodings of ℕ and List ℕ into bitstrings).

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Integer_factorization) -/
@[category research open, AMS 68]
theorem isPolyTime_primeFactorsList : answer(sorry) ↔ IsPolyTime Nat.primeFactorsList := by
  sorry

end PolyTime
