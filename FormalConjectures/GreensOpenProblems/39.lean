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
# Green's Open Problem 39

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.39)
- [BJR11] Bollobás, Béla, Svante Janson, and Oliver Riordan. "On covering by translates of a set."
  Random Structures & Algorithms 38.1‐2 (2011): 33-67.
-/

open Filter Topology
open scoped Pointwise

namespace Green39

/--
The proportion of subsets of $\mathbb{Z}/p\mathbb{Z}$ of size $k$ that can cover
$\mathbb{Z}/p\mathbb{Z}$ using at most $c$ translates.

If p = 0 or k > p, return 0 by convention.
-/
def proportionCoverable (p k c : ℕ) : ℚ :=
  if h : p = 0 then 0
  else if k > p then 0
  else
    have : NeZero p := ⟨h⟩
    let S : Finset (Finset (ZMod p)) := Finset.powersetCard k Finset.univ
    let coverable := S.filter (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ)
    (coverable.card : ℚ) / (S.card : ℚ)

@[category test, AMS 5 60]
theorem proportionCoverable_p_p_1 : proportionCoverable 3 3 1 = 1 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_t_0 : proportionCoverable 5 2 0 = 0 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_2_1_2 : proportionCoverable 2 1 2 = 1 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_3_1_2 : proportionCoverable 3 1 2 = 0 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_a_gt_p : proportionCoverable 3 4 2 = 0 := by native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_7_4_2 :
    proportionCoverable 7 4 2 = (3 : ℚ) / 5 := by
  native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_11_3_4 :
    proportionCoverable 11 3 4 = (1 : ℚ) / 3 := by
  native_decide

@[category test, AMS 5 60]
theorem proportionCoverable_11_4_3 :
    proportionCoverable 11 4 3 = (1 : ℚ) / 6 := by
  native_decide

/--
If $A \subset \mathbb{Z}/p\mathbb{Z}$ is random, $|A| = \sqrt{p}$, can we almost surely cover
$\mathbb{Z}/p\mathbb{Z}$ with $100\sqrt{p}$ translates of $A$? [Gr24]
-/
@[category research open, AMS 5 60]
theorem green_39 : answer(sorry) ↔
    Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := Nat.sqrt p
        let c := 100 * k
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  sorry

/--
"I do not know how to answer this even with 100 replaced by 1.01." [Gr24]"
-/
@[category research open, AMS 5 60]
theorem green_39.variant_101 : answer(sorry) ↔
    Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := Nat.sqrt p
        let c := ⌊1.01 * (k : ℝ)⌋₊
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  sorry




/--
If `k * c < p`, then no subset of size `k` can cover `ZMod p` using at most `c` translates.
Thus the proportion of such subsets is 0.
-/
@[category API, AMS 5 60]
lemma proportionCoverable_eq_zero {p k c : ℕ} (h : k * c < p) : proportionCoverable p k c = 0 :=
  /-
  We unfold the definition of `proportionCoverable`. If `p = 0` or `k > p`, it is 0 by definition.
  Otherwise, we consider the set of coverable subsets. For any `A` of size `k` and `T` of size `≤ c`,
  the size of `A + T` is at most `k * c`. Since `k * c < p`, `A + T` cannot be the whole space `ZMod p`.
  Thus the set of coverable subsets is empty, and the proportion is 0.
  -/
  by
  unfold proportionCoverable
  split_ifs with h1 h2
  · rfl
  · rfl
  · haveI : NeZero p := ⟨h1⟩
    have h_cov : (Finset.filter (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ) (Finset.powersetCard k Finset.univ)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      by_contra h_not_empty
      have ⟨A, hA⟩ : (Finset.filter (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ) (Finset.powersetCard k Finset.univ)).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_not_empty
      rw [Finset.mem_filter] at hA
      rcases hA with ⟨hA1, T, hT1, hT2⟩
      rw [Finset.mem_powersetCard] at hA1
      have h_card : (A + T).card ≤ A.card * T.card := Finset.card_add_le
      rw [hT2] at h_card
      have h_univ_card : (Finset.univ : Finset (ZMod p)).card = p := ZMod.card p
      rw [h_univ_card] at h_card
      have h_bound : A.card * T.card ≤ k * c := Nat.mul_le_mul hA1.2.le hT1
      have h_contra : p ≤ k * c := le_trans h_card h_bound
      linarith
    simp [h_cov]
/--
For any constant `C`, for sufficiently large `p`, we have `⌊p^(1/4)⌋ * ⌊C * p^(1/4)⌋ < p`.
-/
@[category API, AMS 5 60]
lemma eventually_k_c_lt_p (C : ℝ) : ∀ᶠ (p : ℕ) in atTop, ⌊(p : ℝ) ^ (1/4 : ℝ)⌋₊ * ⌊C * (p : ℝ) ^ (1/4 : ℝ)⌋₊ < p :=
  /-
  We can bound the product by `p^(1/4) * C * p^(1/4) = C * p^(1/2)`.
  For large enough `p` (specifically `p > C^2`), `C * p^(1/2) < p`.
  Thus the product is strictly less than `p`.
  -/
  by
  rw [Filter.eventually_atTop]
  use ⌊max 0 (C ^ 2)⌋₊ + 1
  intro p hp
  have hp2 : ⌊max 0 (C ^ 2)⌋₊ + 1 ≤ p := by omega
  have hp_pos : (0 : ℝ) < p := by
    have : 1 ≤ p := by omega
    exact_mod_cast this
  by_cases hC : 0 ≤ C * (p : ℝ) ^ (1/4 : ℝ)
  · have h_k : (⌊(p : ℝ) ^ (1/4 : ℝ)⌋₊ : ℝ) ≤ (p : ℝ) ^ (1/4 : ℝ) := Nat.floor_le (by positivity)
    have h_c : (⌊C * (p : ℝ) ^ (1/4 : ℝ)⌋₊ : ℝ) ≤ C * (p : ℝ) ^ (1/4 : ℝ) := Nat.floor_le hC
    have h_mul : (⌊(p : ℝ) ^ (1/4 : ℝ)⌋₊ : ℝ) * (⌊C * (p : ℝ) ^ (1/4 : ℝ)⌋₊ : ℝ) ≤ (p : ℝ) ^ (1/4 : ℝ) * (C * (p : ℝ) ^ (1/4 : ℝ)) := by
      apply mul_le_mul h_k h_c (Nat.cast_nonneg _) (by positivity)
    have h_mul2 : (p : ℝ) ^ (1/4 : ℝ) * (C * (p : ℝ) ^ (1/4 : ℝ)) = C * (p : ℝ) ^ (1/2 : ℝ) := by
      calc (p : ℝ) ^ (1/4 : ℝ) * (C * (p : ℝ) ^ (1/4 : ℝ))
        _ = C * ((p : ℝ) ^ (1/4 : ℝ) * (p : ℝ) ^ (1/4 : ℝ)) := by ring
        _ = C * (p : ℝ) ^ ((1/4 : ℝ) + (1/4 : ℝ)) := by
          rw [← Real.rpow_add hp_pos]
        _ = C * (p : ℝ) ^ (1/2 : ℝ) := by norm_num
    rw [h_mul2] at h_mul
    have h_p_sqrt : C * (p : ℝ) ^ (1/2 : ℝ) < p := by
      by_cases hC2 : C ≤ 0
      · have : C * (p : ℝ) ^ (1/2 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC2 (by positivity)
        exact lt_of_le_of_lt this hp_pos
      · push_neg at hC2
        have h_C_sq : C ^ 2 < p := by
          have : max 0 (C ^ 2) < p := by
            calc max 0 (C ^ 2)
              _ < (⌊max 0 (C ^ 2)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
              _ ≤ p := by exact_mod_cast hp2
          exact lt_of_le_of_lt (le_max_right _ _) this
        have h_sqrt : Real.sqrt (C ^ 2) < Real.sqrt p := by
          apply Real.sqrt_lt_sqrt (by positivity) h_C_sq
        have h_C_eq : Real.sqrt (C ^ 2) = C := Real.sqrt_sq hC2.le
        rw [h_C_eq] at h_sqrt
        have : C * Real.sqrt p < Real.sqrt p * Real.sqrt p := by
          apply mul_lt_mul_of_pos_right h_sqrt (Real.sqrt_pos.mpr hp_pos)
        have h_p_eq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by positivity)
        rw [h_p_eq] at this
        have h_rpow_eq : (p : ℝ) ^ (1/2 : ℝ) = Real.sqrt p := by
          rw [Real.sqrt_eq_rpow]
        rw [h_rpow_eq]
        exact this
    have h_final : (⌊(p : ℝ) ^ (1/4 : ℝ)⌋₊ : ℝ) * (⌊C * (p : ℝ) ^ (1/4 : ℝ)⌋₊ : ℝ) < p := lt_of_le_of_lt h_mul h_p_sqrt
    exact_mod_cast h_final
  · push_neg at hC
    have h_c_zero : ⌊C * (p : ℝ) ^ (1/4 : ℝ)⌋₊ = 0 := by
      apply Nat.floor_eq_zero.mpr
      exact lt_trans hC (by norm_num)
    rw [h_c_zero, mul_zero]
    exact_mod_cast hp_pos
/--
Similar questions are interesting with $\sqrt{p}$ replaced by $p^\theta$ for any $\theta \le 1/2$. [Gr24]

NOTE: using $C p^\theta$ translates as stated makes the conjecture trivially false by the pigeonhole
principle. Indeed for a set of size $p^\theta$, we cover at most $C p^{2\theta}$ elements, which is
strictly less than $p$ for $\theta < 1/2$. We interpret the question as asking whether
$O(p^{1-\theta})$ translates suffice. This generalizes the main conjecture where
$\sqrt{p} = p^{1-1/2}$.
-/
@[category research solved, AMS 5 60]
theorem green_39.variant_theta : answer(False) ↔
    ∀ (θ : ℝ), 0 < θ → θ ≤ 1/2 →
    ∃ C > 1, Tendsto
      (fun p : {q : ℕ // q.Prime} ↦
        let k := ⌊(p : ℝ) ^ θ⌋₊
        let c := ⌊C * (p : ℝ) ^ θ⌋₊
        (proportionCoverable p k c : ℝ))
      atTop (𝓝 1) := by
  constructor
  · exact False.elim
  · intro h_forall
    have h1 : 0 < (1/4 : ℝ) := by norm_num
    have h2 : (1/4 : ℝ) ≤ 1/2 := by norm_num
    rcases h_forall (1/4) h1 h2 with ⟨C, hC, hTendsto⟩
    have h_ev_nat := eventually_k_c_lt_p C
    haveI : Nonempty {q : ℕ // q.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
    have h_ev : ∀ᶠ (p : {q : ℕ // q.Prime}) in atTop,
        let k := ⌊(p.val : ℝ) ^ (1/4 : ℝ)⌋₊
        let c := ⌊C * (p.val : ℝ) ^ (1/4 : ℝ)⌋₊
        (proportionCoverable p.val k c : ℝ) = 0 := by
      rw [eventually_atTop] at h_ev_nat ⊢
      rcases h_ev_nat with ⟨N, hN⟩
      have h_prime := Nat.exists_infinite_primes N
      rcases h_prime with ⟨p, hp1, hp2⟩
      use ⟨p, hp2⟩
      intro p' hp'
      have : N ≤ p := by omega
      have hp2_le : p ≤ p'.val := hp'
      have h_lt := hN p'.val (le_trans this hp2_le)
      have h_prop := proportionCoverable_eq_zero h_lt
      exact_mod_cast h_prop
    have h_tendsto_0 : Tendsto
        (fun p : {q : ℕ // q.Prime} ↦
          let k := ⌊(p.val : ℝ) ^ (1/4 : ℝ)⌋₊
          let c := ⌊C * (p.val : ℝ) ^ (1/4 : ℝ)⌋₊
          (proportionCoverable p.val k c : ℝ))
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      exact h_ev.mono (fun x hx => hx.symm)
    have h_eq : (0 : ℝ) = 1 := tendsto_nhds_unique h_tendsto_0 hTendsto
    linarith

end Green39
