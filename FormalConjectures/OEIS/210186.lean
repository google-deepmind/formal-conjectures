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
# Least integer $m > 1$ dividing no sum of two distinct primorials up to $P_n$

For $n \ge 1$, $a(n)$ is the least integer $m > 1$ such that $m$ divides none of $P_i + P_j$ with
$0 < i < j \le n$, where $P_k$ is the product of the first $k$ primes.

*References:*
- [A210186](https://oeis.org/A210186)
-/

@[expose] public section

namespace OeisA210186

/-- Least integer $m > 1$ such that $m$ divides none of $P_i + P_j$ with $0 < i < j \le n$,
where $P_k$ is the $k$-th primorial `Nat.kthPrimorial k`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 1 < m ∧
    ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ¬ (m ∣ (Nat.kthPrimorial i + Nat.kthPrimorial j)) }

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => by omega⟩, fun m hm => hm.1⟩

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hi1 : i = 1 := by omega
    have hj2 : j = 2 := by omega
    subst hi1 hj2
    simp
  · by_contra! hlt
    have hm2 : m = 2 := by have := hm.1; omega
    subst hm2
    have := hm.2 1 2 (by decide) (by decide) (by decide)
    simp at this

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hj_ge : 2 ≤ j := by omega
    interval_cases j
    · have hi1 : i = 1 := by omega
      subst hi1; simp
    · interval_cases i <;> simp
  · by_contra! hlt
    have hm_gt : 1 < m := hm.1
    interval_cases m
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 2 3 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this

@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hj_ge : 2 ≤ j := by omega
    interval_cases j
    · have hi1 : i = 1 := by omega
      subst hi1; simp
    · interval_cases i <;> simp
    · interval_cases i <;> simp
  · by_contra! hlt
    have hm_gt : 1 < m := hm.1
    interval_cases m
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 2 3 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 3 4 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 2 3 (by decide) (by decide) (by decide); simp at this

@[category test, AMS 11]
theorem a_5 : a 5 = 11 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hj_ge : 2 ≤ j := by omega
    interval_cases j
    · have hi1 : i = 1 := by omega
      subst hi1; simp
    · interval_cases i <;> simp
    · interval_cases i <;> simp
    · interval_cases i <;> simp
  · by_contra! hlt
    have hm_gt : 1 < m := hm.1
    interval_cases m
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 2 3 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 3 4 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 2 3 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 4 5 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 1 2 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 2 3 (by decide) (by decide) (by decide); simp at this
    · have := hm.2 3 4 (by decide) (by decide) (by decide); simp at this

/--
"Conjecture: all the terms are primes."
- _Zhi-Wei Sun_, Mar 18 2012
-/
@[category research open, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 1 ≤ n) : (a n).Prime := by
  sorry

/--
"Conjecture: $a(n) < n^2$ for all $n > 1$."
- _Zhi-Wei Sun_, Mar 18 2012
-/
@[category research open, AMS 11]
theorem conjecture_2 (n : ℕ) (hn : 1 < n) : a n < n ^ 2 := by
  sorry

end OeisA210186
