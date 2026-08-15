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

import FormalConjectures.Util.ProblemImports

open Nat

/--
A376930: $a(0)=0, a(1)=1$; for $n>1$, $a(n) = a(n-1)+a(n-2)$, except where $a(n-1)$ is a prime greater than 2, in which case $a(n) = a(n-1)-a(n-2)$.
-/
noncomputable def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an_1 := a (n + 1)
  let an_2 := a n
  if Nat.Prime an_1 ∧ an_1 > 2 then
    an_1 - an_2
  else
    an_1 + an_2

/--
oeis_376930_conjecture_0: It is not known if the sequence contains any negative terms (which may happen if two primes are adjacent or separated by one other term).

Formalization: Since the sequence is defined in $\mathbb{N}$, all terms are non-negative by definition. The conjecture's mathematical content is that whenever the subtraction rule $a(n+2) = a(n+1) - a(n)$ is applied, the result in $\mathbb{Z}$ is non-negative. In the context of $\mathbb{N}$ arithmetic, this is equivalent to asserting that $a(n+1) \ge a(n)$.
-/
theorem oeis_376930_conjecture_0 :
  ∀ n : ℕ, (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) → a (n + 1) ≥ a n := by sorry
