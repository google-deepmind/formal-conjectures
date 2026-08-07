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

open Finset Nat

/--
A370092: $a(0) = 1$,
$$a(n) = (-1)^n + \frac{1}{2} \sum_{j=1}^n (1-(-1)^j-(-2)^j) \binom{n}{j} a(n-j) \quad \text{for } n > 0$$
The sequence is defined in $\mathbb{Q}$ to directly translate the recurrence relation.
The terms are conjectured to be integers.
-/
noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    -- The sum is over j from 1 to m_plus_one. k runs from 0 to m.
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1 -- j is the index for the sum

      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j

      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val


theorem a_zero : a 0 = 1 := by
  sorry

theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 3 := by
  sorry

theorem a_three : a 3 = 16 := by
  sorry


-- We formally define an eventually periodic sequence.
/-- A sequence `f` is eventually periodic with period `P` if after some index `N`, `f(n + P) = f(n)`. -/
def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

/--
The reduction of `a n` modulo `k`. Since all terms of `a n` are integers, we take the
numerator of the rational number representation, which is the integer value, and reduce it modulo `k`.
This requires `k > 0`, which is guaranteed by `2 < k`.
-/
noncomputable def a_mod_k (k : ℕ) (n : ℕ) : ZMod k :=
  Int.cast (a n).num

/--
%C A370092 Conjecture: Let k > 2 be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k).
-/
theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  sorry
