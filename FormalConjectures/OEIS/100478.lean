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

/-!
# Pentanacci pi sequence

Pentanacci $\pi$ sequence: $a(1)=a(2)=a(3)=a(4)=a(5)=1$;
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.

*References:*
- [A100478](https://oeis.org/A100478)
-/

namespace OeisA100478

open scoped Nat.Prime

/-- 
The primary defining sequence `a`.
Pentanacci $\pi$ sequence: $a(1)=a(2)=a(3)=a(4)=a(5)=1$;
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.
Note on indices: for $n \ge 0$, $a(n)$ corresponds to $A_{n+1}$ in the OEIS sequence.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | i + 5 =>
    let sum_terms := a (i + 4) + a (i + 3) + a (i + 2) + a (i + 1) + a i
    π sum_terms

/--
A general sequence defined by the Pentanacci $\pi$ recurrence, starting with arbitrary initial values $v: \text{Fin } 5 \to \mathbb{N}$.
The sequence $a_{general}(v, n)$ is the n-th term (0-indexed).
-/
noncomputable def a_general (v : Fin 5 → ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | i + 5 =>
    let sum_terms := a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) + a_general v (i + 1) + a_general v i
    π sum_terms

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_3 : a 3 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_4 : a 4 = 1 := by rfl

/-- 
Starting with other values of a(1), a(2), a(3), a(4), a(5) what behaviors are possible? Does the sequence always stick at a single integer after some point, or can it go into a loop, or is there a third pattern? 
-/
@[category research open, AMS 11]
theorem main_conjecture :
  ∀ (v : Fin 5 → ℕ), (∀ i, v i > 0) →
  ∃ N P : ℕ, P > 0 ∧ (∀ n, n ≥ N → a_general v (n + P) = a_general v n) := by
  sorry

end OeisA100478
