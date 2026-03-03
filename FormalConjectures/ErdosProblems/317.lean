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
# Erdős Problem 317

*Reference:* [erdosproblems.com/317](https://www.erdosproblems.com/317)
-/

namespace Erdos317
open Finset
open Filter

/--
Is there some constant $c>0$ such that for every $n\geq 1$ there exists some $\delta_k\in \{-1,0,1\}$ for $1\leq k\leq n$ with
\[0< \left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert < \frac{c}{2^n}?\]
-/
@[category research open, AMS 11]
theorem erdos_317 : answer(sorry) ↔
    ∃ c > 0, ∀ n ≥ 1, ∃ δ : Fin n → ℚ,
      Set.range δ ⊆ {-1, 0, 1} ∧
      letI lhs : ℝ := |∑ k, (δ k) / (k + 1)|
      0 < lhs ∧ lhs < c / 2^n := by
  sorry

/--
Is it true that for sufficiently large $n$, for any $\delta_k\in \{-1,0,1\}$,
\[\left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert > \frac{1}{[1,\ldots,n]}\]
whenever the left-hand side is not zero?
-/
@[category research open, AMS 11]
theorem erdos_317.variants.claim2 : answer(sorry) ↔
    ∀ᶠ n in atTop, ∀ δ : (Fin n) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs > 1 / (Icc 1 n).lcm id := by
  sorry

private lemma den_mul_q (q : ℚ) : (q.den : ℚ) * q = q.num := by
  have h := q.num_div_den; field_simp at h ⊢; linarith

private lemma den_mul_abs (q : ℚ) : (q.den : ℚ) * |q| = |(q.num : ℚ)| := by
  have hden_pos : (0 : ℚ) < q.den := by exact_mod_cast q.pos
  have hden_ne : (q.den : ℚ) ≠ 0 := ne_of_gt hden_pos
  have : |q| = |(q.num : ℚ)| / (q.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    rw [abs_div, abs_of_pos hden_pos]
  rw [this, mul_div_cancel₀ _ hden_ne]

private lemma rat_ge_one_div_of_den_dvd (q : ℚ) (L : ℕ) (hL : 0 < L) (hq : q ≠ 0)
    (hdvd : (q.den : ℕ) ∣ L) : (1 : ℚ) / L ≤ |q| := by
  rw [div_le_iff₀' (by exact_mod_cast hL : (L : ℚ) > 0)]
  have hnum_ne_zero : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hnum_abs : (1 : ℤ) ≤ |q.num| := Int.one_le_abs hnum_ne_zero
  obtain ⟨m, hm⟩ := hdvd
  have hm_pos : 1 ≤ m := by
    by_contra h; push_neg at h
    have : m = 0 := Nat.lt_one_iff.mp h
    simp [this, hm] at hL
  have key : (q.den : ℚ) * |q| ≥ 1 := by
    rw [den_mul_abs]; exact_mod_cast hnum_abs
  have hden_cast : (q.den : ℚ) ≤ (L : ℚ) := by
    rw [hm]; push_cast
    exact le_mul_of_one_le_right (by exact_mod_cast q.pos.le) (by exact_mod_cast hm_pos)
  calc (1 : ℚ) ≤ q.den * |q| := key
    _ ≤ L * |q| := mul_le_mul_of_nonneg_right hden_cast (abs_nonneg q)

private lemma kp1_dvd_lcm (n : ℕ) (k : Fin n) : (k.val + 1) ∣ (Icc 1 n).lcm id := by
  refine Finset.dvd_lcm (f := id) ?_
  simp only [mem_Icc, id]
  omega

private lemma int_of_den_dvd (q : ℚ) (L : ℕ) (h : q.den ∣ L) : ∃ m : ℤ, (m : ℚ) = L * q := by
  obtain ⟨k, hk⟩ := h
  use k * q.num
  have hkq : (L : ℚ) * q = ↑k * ((q.den : ℚ) * q) := by
    have : (L : ℚ) = (q.den : ℚ) * k := by exact_mod_cast hk
    rw [this]; ring
  rw [hkq, den_mul_q]
  push_cast; ring

private lemma den_dvd_of_int (q : ℚ) (L : ℕ) (h : ∃ m : ℤ, (m : ℚ) = L * q) : q.den ∣ L := by
  obtain ⟨m, hm⟩ := h
  have hmq : (m : ℤ) * q.den = L * q.num := by
    have : (m : ℚ) * q.den = L * q.num := by
      calc (m : ℚ) * q.den = L * q * q.den := by rw [← hm]
        _ = L * (q.den * q) := by ring
        _ = L * q.num := by rw [den_mul_q]
    exact_mod_cast this
  have hd : (q.den : ℤ) ∣ (L : ℤ) * q.num := ⟨m, by linarith⟩
  have hcop : IsCoprime (q.den : ℤ) q.num := q.isCoprime_num_den.symm
  have := hcop.dvd_of_dvd_mul_right hd
  exact_mod_cast this

private lemma sum_den_dvd_lcm (n : ℕ) (δ : Fin n → ℚ)
    (hδ : δ '' Set.univ ⊆ ({-1, 0, 1} : Set ℚ)) :
    (∑ k : Fin n, (δ k : ℚ) / (↑k.val + 1)).den ∣ (Icc 1 n).lcm id := by
  apply den_dvd_of_int
  set L := (Icc 1 n).lcm id
  rw [Finset.mul_sum]
  have hterms : ∀ k : Fin n, ∃ m : ℤ, (m : ℚ) = L * (δ k / (↑k.val + 1)) := by
    intro k
    have hδk : δ k ∈ ({-1, 0, 1} : Set ℚ) := hδ ⟨k, Set.mem_univ k, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδk
    have hdvd : (k.val + 1) ∣ L := kp1_dvd_lcm n k
    obtain ⟨j, hj⟩ := hdvd
    rcases hδk with h | h | h <;> rw [h]
    · use -j; push_cast [hj]; field_simp
    · use 0; push_cast; ring
    · use j; push_cast [hj]; field_simp
  choose g hg using hterms
  use Finset.univ.sum g
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  exact hg k

/--
Inequality in `erdos_317.variants.claim2` is obvious, the problem is strict inequality.
-/
@[category undergraduate, AMS 11]
lemma claim2_inequality : ∀ᶠ n in atTop,
    ∀ δ : (Fin n) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs ≥ 1 / (Icc 1 n).lcm id := by
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n _hn δ hδ => ?_⟩
  set S := ∑ k : Fin n, ((δ k : ℚ) / (↑k.val + 1)) with hS_def
  show |S| ≠ 0 → |S| ≥ 1 / (Icc 1 n).lcm id
  intro hne
  have hS_ne : S ≠ 0 := by intro h; simp [h] at hne
  apply rat_ge_one_div_of_den_dvd
  · simp only [Nat.pos_iff_ne_zero]
    intro h; simp [Finset.lcm_eq_zero_iff] at h
  · exact hS_ne
  · exact sum_den_dvd_lcm n δ hδ

/--
`erdos_317.variants.claim2` fails for small $n$, for example
\[\frac{1}{2}-\frac{1}{3}-\frac{1}{4}=-\frac{1}{12}.\]
-/
@[category graduate, AMS 11]
theorem erdos_317.variants.counterexample : ¬ (∀  δ : (Fin 4) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs > (1 : ℚ) / ((Icc 1 4).lcm id : ℕ)) := by
  push_neg
  use ![0, 1, -1, -1]
  norm_num [Finset.sum]
  exact ⟨by grind, by simp; rfl⟩

end Erdos317
