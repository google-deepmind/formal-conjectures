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

/-! # Erdős Problem 349

*Reference:* [erdosproblems.com/349](https://www.erdosproblems.com/349)
-/

namespace Erdos349

open Set Filter Real Nat Function


/--
This defines the core property of the problem: For what values of $t,\alpha \in (0,\infty)$
is the sequence $\lfloor t\alpha^n\rfloor$ complete?
-/
def IsGoodPair (t α : ℝ) : Prop :=
  IsAddComplete (range (fun n ↦ ⌊t * α ^ n⌋))

/--
For what values of $t,\alpha \in (0,\infty)$ is the sequence $\lfloor t\alpha^n\rfloor$ complete
(that is, all sufficiently large integers are the sum of distinct integers of the form $\lfloor t\alpha^n\rfloor$)?
-/
@[category research open, AMS 11]
theorem erdos_349 :
    {(t, α) | 0 < t ∧ 0 < α ∧ IsGoodPair t α} = answer(sorry) := by
  sorry

/--
It seems likely that the sequence is complete for all
for all $t>0$ and all $1 < \alpha < \frac{1+\sqrt{5}}{2}$.
-/
@[category research open, AMS 11]
theorem complete_for_alpha_in_Ioo_one_to_goldenRatio (t α : ℝ) (ht : 0 < t)
    (hα : α ∈ Set.Ioo 1 ((1 + √5) / 2)) : IsGoodPair t α := by
  sorry

/--
For any $k$ there exists some $t_k\in (0,1)$ such that the set of $\alpha$
such that the sequence $\lfloor t_k\alpha^n\rfloor$ is complete consists of at least $k$
disjoint line segments.
-/
@[category research solved, AMS 11]
theorem exists_t_for_k_disjoint_segments (k : ℕ) :
    ∃ t ∈ Ioo 0 1, ∃ (ι : Type), k ≤ (Set.univ : Set ι).encard ∧ ∃ I : ι → Set ℝ,
      (∀ i, 2 ≤ (I i).encard ∧ (I i).Nonempty ∧ IsConnected (I i)) ∧
      Pairwise (Disjoint on I) ∧ (⋃ i, I i) ⊆ {α | α > 0 ∧ IsGoodPair t α} := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are odd infinitely
often and even infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_349.variants.floor_3_halves_odd :
    answer(sorry) ↔ {n | Odd ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/--
Is it true that the terms of the sequence $\lfloor (3/2)^n\rfloor$ are even infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_349.variants.floor_3_halves_even :
    answer(sorry) ↔ {n | Even ⌊(3/2 : ℝ) ^ n⌋}.Infinite := by
  sorry

/-- For α>2 and any t>0, ⌊t·αⁿ⌋ is not additively complete; equivalently (t,α) is not a
    "good pair". A partial result on the open Erdős 349: it complements
    `complete_for_alpha_in_Ioo_one_to_goldenRatio`. -/
@[category research solved, AMS 11]
theorem alpha_gt_two_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα : 2 < α) : ¬ IsGoodPair t α := by
  unfold IsGoodPair
  set f : ℕ → ℤ := fun n => ⌊t * α ^ n⌋ with hf
  -- Basic facts about α.
  have hα0 : (0 : ℝ) < α := by linarith
  have hα1 : (1 : ℝ) < α := by linarith
  have hα1' : (1 : ℝ) ≤ α := le_of_lt hα1
  have hαm1 : (0 : ℝ) < α - 1 := by linarith
  -- (1) nonneg: 0 ≤ f n.
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    rw [hf]
    simp only
    rw [Int.floor_nonneg]
    positivity
  -- a real upper bound on each term as a real.
  have hterm_le : ∀ k, (f k : ℝ) ≤ t * α ^ k := by
    intro k
    rw [hf]
    exact Int.floor_le _
  -- (2) monotone.
  have hmono : Monotone f := by
    intro n m hnm
    rw [hf]
    simp only
    apply Int.floor_le_floor
    apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
    exact pow_le_pow_right₀ hα1' hnm
  -- (3) partial sum.
  set S : ℕ → ℤ := fun n => ∑ k ∈ Finset.range (n + 1), f k with hS
  -- geometric bound: (S n : ℝ) ≤ t * α^(n+1) / (α - 1).
  have hSbound : ∀ n, (S n : ℝ) ≤ t * α ^ (n + 1) / (α - 1) := by
    intro n
    have h1 : (S n : ℝ) = ∑ k ∈ Finset.range (n + 1), (f k : ℝ) := by
      rw [hS]; push_cast; rfl
    rw [h1]
    have h2 : ∑ k ∈ Finset.range (n + 1), (f k : ℝ)
        ≤ ∑ k ∈ Finset.range (n + 1), t * α ^ k := by
      apply Finset.sum_le_sum
      intro k _
      exact hterm_le k
    refine le_trans h2 ?_
    have h3 : ∑ k ∈ Finset.range (n + 1), t * α ^ k
        = t * ((α ^ (n + 1) - 1) / (α - 1)) := by
      rw [← Finset.mul_sum, geom_sum_eq (by linarith : α ≠ 1)]
    rw [h3]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
    apply div_le_div_of_nonneg_right (by linarith) hαm1.le
  -- (5) the gap: find a single large n with both M ≥ N and a_{n+1} ≥ S n + 2.
  rw [IsAddComplete, Filter.not_eventually]
  rw [Filter.frequently_atTop]
  intro N
  -- tendsto: t·α^(n+1)·(α-2)/(α-1) - 2 → ∞.
  have htend : Tendsto (fun n : ℕ => t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2)
      atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => α ^ (n + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hα1).comp (tendsto_add_atTop_nat 1)
    have hc2 : (0 : ℝ) < (α - 2) / (α - 1) := by
      apply _root_.div_pos <;> linarith
    have h1 : Tendsto (fun n : ℕ => t * α ^ (n + 1)) atTop atTop :=
      hpow.const_mul_atTop ht
    have h2 : Tendsto (fun n : ℕ => t * α ^ (n + 1) * ((α - 2) / (α - 1))) atTop atTop :=
      h1.atTop_mul_const hc2
    exact tendsto_atTop_add_const_right atTop (-2 : ℝ)
      (by simpa [sub_eq_add_neg] using h2)
  -- S n ≥ N via S n ≥ a_n ≥ t·α^n - 1 → ∞.
  have htend2 : Tendsto (fun n : ℕ => t * α ^ n - 1) atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => α ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hα1
    have h1 : Tendsto (fun n : ℕ => t * α ^ n) atTop atTop :=
      hpow.const_mul_atTop ht
    exact tendsto_atTop_add_const_right atTop (-1 : ℝ)
      (by simpa [sub_eq_add_neg] using h1)
  -- Get n with g n ≥ max(N+2, 3)  AND  t·α^n - 1 ≥ N.
  have hev := (htend.eventually_ge_atTop (max ((N : ℝ) + 2) 3)).and
      (htend2.eventually_ge_atTop ((N : ℝ)))
  obtain ⟨n, hn, hn2⟩ := hev.exists
  have hn' : (N : ℝ) + 2 ≤ t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 :=
    le_trans (le_max_left _ _) hn
  have hn3 : (3 : ℝ) ≤ t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 :=
    le_trans (le_max_right _ _) hn
  -- real lower bound for a_{n+1}.
  have ha_lb : t * α ^ (n + 1) - 1 < (f (n + 1) : ℝ) := by
    have := Int.sub_one_lt_floor (t * α ^ (n + 1))
    rw [hf]; exact this
  have hreal : (f (n + 1) : ℝ) - (S n : ℝ) - 1
      > t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 := by
    have hsb := hSbound n
    have key : t * α ^ (n + 1) * ((α - 2) / (α - 1))
        = t * α ^ (n + 1) - t * α ^ (n + 1) / (α - 1) := by
      field_simp
      ring
    rw [key]
    linarith [ha_lb, hsb]
  have hcombine : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > (N : ℝ) + 2 := by
    linarith [hreal, hn']
  have hgapR : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > 3 := by
    linarith [hreal, hn3]
  have hgap : f (n + 1) ≥ S n + 2 := by
    have : ((f (n + 1) - (S n) : ℤ) : ℝ) ≥ ((2 : ℤ) : ℝ) := by
      push_cast; linarith [hgapR]
    have h2 : (f (n + 1) - (S n) : ℤ) ≥ (2 : ℤ) := by exact_mod_cast this
    linarith
  have hint : (f (n + 1) : ℝ) - (S n : ℝ) - 1 ≥ (N : ℝ) + 2 := le_of_lt hcombine
  have hZ : (f (n + 1)) - (S n) - 1 ≥ N + 2 := by
    have : ((f (n + 1) - (S n) - 1 : ℤ) : ℝ) ≥ ((N + 2 : ℤ) : ℝ) := by
      push_cast; linarith [hint]
    exact_mod_cast this
  -- The missed value M := S n + 1.  S n ≥ N : since S n ≥ a_n ≥ t·α^n - 1 ≥ N.
  have hSn_lb : (S n : ℝ) ≥ t * α ^ n - 1 := by
    have hlast : f n ≤ S n := by
      rw [hS]
      apply Finset.single_le_sum (fun i _ => hnonneg i)
      simp
    have h1 : (f n : ℝ) ≥ t * α ^ n - 1 := by
      have := Int.sub_one_lt_floor (t * α ^ n)
      have : (t * α ^ n) - 1 ≤ (⌊t * α ^ n⌋ : ℝ) := le_of_lt this
      rw [hf]; simpa using this
    have h2 : (f n : ℝ) ≤ (S n : ℝ) := by exact_mod_cast hlast
    linarith
  have hSnN : (S n) ≥ N := by
    have : (S n : ℝ) ≥ (N : ℝ) := le_trans hn2 hSn_lb
    exact_mod_cast this
  refine ⟨S n + 1, ?_, ?_⟩
  · -- M ≥ N
    linarith
  · -- M := S n + 1 ∉ subsetSums (range f).
    rintro ⟨B, hBsub, hBsum⟩
    have hBnonneg : ∀ b ∈ B, (0 : ℤ) ≤ b := by
      intro b hb
      have : b ∈ Set.range f := hBsub hb
      obtain ⟨m, rfl⟩ := this
      exact hnonneg m
    set P : ℤ := f (n + 1) with hP
    by_cases hcase : ∃ b ∈ B, P ≤ b
    · obtain ⟨b, hbB, hPb⟩ := hcase
      have hge : P ≤ ∑ i ∈ B, i := by
        calc P ≤ b := hPb
          _ ≤ ∑ i ∈ B, i := Finset.single_le_sum (fun i _ => hBnonneg i ‹_›) hbB
      have : S n + 1 ≥ P := by rw [hBsum]; exact hge
      have : S n + 1 ≥ S n + 2 := le_trans hgap this
      omega
    · have hlt : ∀ b ∈ B, b < P := by
        intro b hb
        by_contra hc
        exact hcase ⟨b, hb, not_lt.mp hc⟩
      have hBsubimg : B ⊆ (Finset.range (n + 1)).image f := by
        intro b hb
        have hbP : b < P := hlt b hb
        have : b ∈ Set.range f := hBsub hb
        obtain ⟨m, rfl⟩ := this
        have hmle : m ≤ n := by
          by_contra hmn
          have : f (n + 1) ≤ f m := hmono (by omega)
          rw [← hP] at this
          omega
        rw [Finset.mem_image]
        exact ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
      have himg_le : ∑ u ∈ (Finset.range (n + 1)).image f, u ≤ S n := by
        have h := Finset.sum_image_le_of_nonneg
          (s := Finset.range (n + 1)) (g := f) (f := fun x : ℤ => x)
          (fun u hu => by
            rw [Finset.mem_image] at hu
            obtain ⟨m, _, rfl⟩ := hu
            exact hnonneg m)
        simpa [hS] using h
      have hBsum_le : ∑ i ∈ B, i ≤ S n := by
        calc ∑ i ∈ B, i
            ≤ ∑ u ∈ (Finset.range (n + 1)).image f, u :=
              Finset.sum_le_sum_of_subset_of_nonneg hBsubimg
                (fun i hi _ => by
                  rw [Finset.mem_image] at hi
                  obtain ⟨m, _, rfl⟩ := hi
                  exact hnonneg m)
          _ ≤ S n := himg_le
      rw [← hBsum] at hBsum_le
      omega

end Erdos349
