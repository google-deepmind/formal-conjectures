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
module

public import FormalConjecturesUtil

/-!
# Primorial squared plus one

The sequence $a(n)$ is defined by $a(n) = (p_n\#)^2 + 1$, where $p_n\# = \prod_{k=0}^{n-1} p_k$
is the $n$-th primorial (A002110).

*References:*
- [A189409](https://oeis.org/A189409)
-/

@[expose] public section

namespace OeisA189409

/-- The sequence $a(n) = (p_n\#)^2 + 1$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.kthPrimorial n) ^ 2 + 1

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by simp [a]

@[category test, AMS 11]
theorem a_1 : a 1 = 5 := by simp [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 37 := by simp [a]

@[category test, AMS 11]
theorem a_3 : a 3 = 901 := by simp [a]

@[category test, AMS 11]
theorem a_4 : a 4 = 44101 := by simp [a]

/--
It is unknown whether or not numbers in this sequence are always squarefree.
- _John M. Campbell_, Apr 21 2011
-/
@[category research open, question, AMS 11]
theorem conjecture_1 : ∀ n : ℕ, Squarefree (a n) := by
  sorry

/--
It is unknown whether or not there exist infinitely many primes in this sequence.
- _John M. Campbell_, Apr 21 2011
-/
@[category research open, question, AMS 11]
theorem conjecture_2 : Set.Infinite {n : ℕ | (a n).Prime} := by
  sorry

end OeisA189409
