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
# Erdős Problem 730

*References:*
  - [erdosproblems.com/730](https://www.erdosproblems.com/730)
  - [A129515](https://oeis.org/A129515)
-/
abbrev S :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}


namespace Erdos730

/--
Are there infinitely many pairs of integers $n < m$ such that $\binom{2n}{n}$
and $\binom{2m}{m}$ have the same set of prime divisors?
-/
@[category research open, AMS 11]
theorem erdos_730 : answer(sorry) ↔ S.Infinite := by
  sorry

@[category API]
lemma dvd_of_dvd_pow2 {p x : ℕ} (hp : Nat.Prime p) (h : p ∣ x * x) : p ∣ x :=
  or_self_iff.1 (hp.dvd_mul.1 h)

@[category API]
lemma dvd_of_dvd_pow3 {p x : ℕ} (hp : Nat.Prime p) (h : p ∣ x * (x * x)) : p ∣ x := by
  cases hp.dvd_mul.1 h with
  | inl h1 => exact h1
  | inr h2 => exact dvd_of_dvd_pow2 hp h2

@[category API]
lemma dvd_of_dvd_pow4 {p x : ℕ} (hp : Nat.Prime p) (h : p ∣ x * (x * (x * x))) : p ∣ x := by
  cases hp.dvd_mul.1 h with
  | inl h1 => exact h1
  | inr h2 => exact dvd_of_dvd_pow3 hp h2

@[category API]
lemma dvd_of_dvd_pow5 {p x : ℕ} (hp : Nat.Prime p) (h : p ∣ x * (x * (x * (x * x)))) : p ∣ x := by
  cases hp.dvd_mul.1 h with
  | inl h1 => exact h1
  | inr h2 => exact dvd_of_dvd_pow4 hp h2

@[category API]
lemma dvd_of_dvd_pow6 {p x : ℕ} (hp : Nat.Prime p) (h : p ∣ x * (x * (x * (x * (x * x))))) : p ∣ x := by
  cases hp.dvd_mul.1 h with
  | inl h1 => exact h1
  | inr h2 => exact dvd_of_dvd_pow5 hp h2

set_option maxRecDepth 1000000

@[category test]
lemma check_87_88 : (87, 88) ∈ S := by
  dsimp [S]
  norm_num [Finset.ext_iff, Nat.choose_eq_zero_iff, Nat.centralBinom]
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  intro p hp
  refine Iff.intro ?_ ?_
  · exact fun h' => dvd_of_dvd_pow2 hp (h'.trans (by exact of_decide_eq_true (by decide)))
  · exact fun h' => dvd_of_dvd_pow3 hp (h'.trans (by exact of_decide_eq_true (by decide)))

@[category test]
lemma check_607_608 : (607, 608) ∈ S := by
  dsimp [S]
  norm_num [Finset.ext_iff, Nat.choose_eq_zero_iff, Nat.centralBinom]
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  intro p hp
  refine Iff.intro ?_ ?_
  · exact fun h' => dvd_of_dvd_pow3 hp (h'.trans (by exact of_decide_eq_true (by decide)))
  · exact fun h' => dvd_of_dvd_pow6 hp (h'.trans (by exact of_decide_eq_true (by decide)))

/--
For example, $(87,88)$ and $(607,608)$ are such pairs.
-/
@[category high_school, AMS 11]
theorem erdos_730.variants.explicit_pairs :
    {(87, 88), (607, 608)} ⊆ S := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact check_87_88
  · exact check_607_608

/--
There are examples where $(n, m) ∈ S$ with $m ≠ n + 1$.

(Found by AlphaProof, although it was implicit already in [A129515])
-/
@[category research formally solved using formal_conjectures at
    "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/730.lean", AMS 11]
theorem erdos_730.variants.delta_ne_one : ∃ (n m : ℕ), (n, m) ∈ S ∧ m ≠ n + 1 := by
  dsimp [S]
  use 10003
  use 10005
  norm_num [Finset.ext_iff, Nat.choose_eq_zero_iff, Nat.centralBinom]
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  intro p hp
  constructor
  all_goals exact fun h' => or_self_iff.1 (hp.dvd_mul.1 (
    h'.trans (by refine' of_decide_eq_true (by constructor : _ = ↑_))))


end Erdos730
