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
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import FormalConjecturesForMathlib.Algebra.Order.Group.Pointwise.Interval
public import FormalConjecturesForMathlib.Data.Set.Interval
public import FormalConjecturesForMathlib.Order.Interval.Finset.Basic
public import FormalConjecturesForMathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

@[expose] public section

open Filter

open scoped Topology

namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

theorem partialDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : S.partialDensity A b ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ inter_subset_right

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the upper
density of `S` (relative to a set `A`) to be the limsup of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the lower
density of `S` (relative to a set `A`) to be the liminf of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

theorem lowerDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : S.lowerDensity A ≤ 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, Set.lowerDensity, Filter.liminf_eq]
  · have : (atTop (α := β)).NeBot := ⟨h⟩
    apply Real.sSup_le (fun x hx ↦ ?_) one_pos.le
    simpa using hx.mono fun y hy ↦ hy.trans (Set.partialDensity_le_one _ _ y)

theorem lowerDensity_nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : 0 ≤ S.lowerDensity A := by
  rw [Set.lowerDensity, Filter.liminf_eq]
  exact (em _).elim (le_csSup · <| .of_forall fun _ ↦ by positivity)
    (Real.sSup_of_not_bddAbove · |>.ge)

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
positive density (relative to a set `A`) if there exists a positive `α : ℝ` such that
`S` has density `α` (relative to a set `A`).
-/
def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

/--
The two-sided partial natural density of a set of integers, counted inside the interval
`[-N, N]`.
-/
noncomputable def intPartialDensity (S : Set ℤ) (N : ℕ) : ℝ :=
  open scoped Classical in
  (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => m ∈ S)).card : ℝ) /
    (2 * (N : ℝ) + 1)

/-- A set of integers has two-sided natural density `α`. -/
def HasIntDensity (S : Set ℤ) (α : ℝ) : Prop :=
  Tendsto (fun N : ℕ => S.intPartialDensity N) atTop (𝓝 α)

@[simp]
theorem intPartialDensity_empty (N : ℕ) : intPartialDensity (∅ : Set ℤ) N = 0 := by
  simp [intPartialDensity]

namespace HasIntDensity

@[simp]
theorem empty : HasIntDensity (∅ : Set ℤ) 0 := by
  simp [HasIntDensity]

end HasIntDensity

namespace HasDensity

-- TODO(mercuris): generalise these to non-univ `A`

/-- In a non-trivial partial order with a least element, the set of all
elements has density one. -/
@[simp]
theorem univ {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
    (@Set.univ β).HasDensity 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, HasDensity]
  · simp [HasDensity, partialDensity]
    let ⟨b, hb⟩ := Set.Iio_eventually_ncard_ne_zero β
    refine tendsto_const_nhds.congr' ?_
    exact (eventually_ge_atTop b).mono fun n hn ↦ (div_self <| mod_cast hb n hn).symm

theorem univ_nat_hasDensity_one : (@Set.univ ℕ).HasDensity 1 := univ

@[simp]
theorem empty {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (A : Set β := Set.univ) :
    Set.HasDensity (∅ : Set β) 0 A := by
  simpa [HasDensity, partialDensity] using tendsto_const_nhds

theorem mono {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β]
    {S T : Set β} {αS αT : ℝ} [(atTop (α := β)).NeBot] (h : S ⊆ T) (hS : S.HasDensity αS)
    (hT : T.HasDensity αT) : αS ≤ αT := by
  rw [HasDensity] at hS hT
  apply le_of_tendsto_of_tendsto hS hT
  filter_upwards [eventually_ge_atTop ⊥] with b hb
  apply div_le_div_of_nonneg_right
  grw [Set.ncard_le_ncard (inter_subset_inter_left _ (inter_subset_inter_left _ h))]
  exact Nat.cast_nonneg _

theorem nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] [(atTop : Filter β).NeBot]
    {S : Set β} {α : ℝ} (h : S.HasDensity α) : 0 ≤ α :=
  le_of_tendsto_of_tendsto' empty h fun b => by simp [div_nonneg, partialDensity]

end Set.HasDensity

namespace Nat

open Set

/--
The natural density of the set of even numbers is `1 / 2`.
-/
theorem hasDensity_even : {n : ℕ | Even n}.HasDensity (1 / 2) := by
  simp [HasDensity, partialDensity]
  have h {n : ℕ} (hn : 1 ≤ n) : (({n : ℕ | Even n} ∩ Iio n).ncard : ℝ) / n =
      if Even n then 2⁻¹ else (n + 1 : ℝ) /  n * 2⁻¹ := by
    split_ifs with h
    · rw [← image_mul_two_Iio_even h, ncard_image_of_injective _
          (mul_right_injective₀ (by simp)), ncard_Iio,
        cast_div_charZero (even_iff_two_dvd.mp h), cast_ofNat,
        div_div_cancel_left' <| cast_ne_zero.2 (by linarith)]
    · replace h : Even (n + 1) := by simpa [Nat.even_add', ← Nat.not_even_iff_odd]
      rw [← image_mul_two_Iio n, ncard_image_of_injective _
          (mul_right_injective₀ (by simp)), ncard_Iio,
        cast_div (even_iff_two_dvd.mp h) (by norm_num), cast_add]; ring
  refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (h hn).symm⟩)
    (Tendsto.if' tendsto_const_nhds ?_)
  replace h : Tendsto (fun (k : ℕ) => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    simpa using Tendsto.const_add (M := ℝ) _ tendsto_one_div_atTop_nhds_zero_nat
  simpa using Tendsto.mul_const _ <|
    Tendsto.congr' (eventually_atTop.2 ⟨1, fun k hk => by field_simp⟩) h

/-- A finite set has natural density zero. -/
theorem hasDensity_zero_of_finite {S : Set ℕ} (h : S.Finite) : S.HasDensity 0 := by
  simp [HasDensity, partialDensity]
  have (n : ℕ) : ((S ∩ Set.Iio n).ncard : ℝ) / n ≤ S.ncard / n := by
    by_cases h₀ : n = 0; simp [h₀]
    exact div_le_div₀ (by simp) (by simpa using Set.ncard_inter_le_ncard_left _ _ h)
      (by simpa using n.pos_of_ne_zero h₀) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat _)
    (fun _ => div_nonneg (cast_nonneg _) (cast_nonneg _)) this

/-- A finite set of natural numbers has density `0` relative to any infinite set `A` of natural
numbers, because the number of elements of `A` below `b` tends to infinity. -/
lemma hasDensity_zero_of_finite_of_infinite {T A : Set ℕ} (hT : T.Finite) (hA : A.Infinite) :
    T.HasDensity 0 A := by
  have hden : Filter.Tendsto (fun b : ℕ => ((A ∩ Set.Iio b).ncard : ℝ)) Filter.atTop
      Filter.atTop := by
    refine tendsto_natCast_atTop_atTop.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun m n hmn => Set.ncard_le_ncard (Set.inter_subset_inter_right _
        (Set.Iio_subset_Iio hmn)) ((Set.finite_Iio n).inter_of_right A)) fun N => ?_)
    obtain ⟨t, htA, htc⟩ := hA.exists_subset_card_eq N
    refine ⟨t.sup id + 1, ?_⟩
    have hsub : (t : Set ℕ) ⊆ A ∩ Set.Iio (t.sup id + 1) := fun x hx =>
      ⟨htA hx, Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)⟩
    simpa [htc] using Set.ncard_le_ncard hsub ((Set.finite_Iio _).inter_of_right A)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hden.const_div_atTop (T.ncard : ℝ)) (fun b => ?_) (fun b => ?_)
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    refine Nat.cast_le.2 ?_
    exact Set.ncard_le_ncard (fun x hx => hx.1.1) hT

/-- A set of positive natural density is infinite. -/
theorem infinite_of_hasDensity_pos {S : Set ℕ} {α : ℝ} (h : S.HasDensity α) (hα : α ≠ 0) :
    S.Infinite :=
  mt hasDensity_zero_of_finite fun h' => hα (tendsto_nhds_unique h h')

end Nat

/-! ## Logarithmic Density -/

section LogarithmicDensity

open Finset Real

/--
A set `A` of natural numbers has logarithmic density `d` if the sequence
$(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
Logarithmic density is a weaker notion than natural density: if a set has natural density `d`,
then it also has logarithmic density `d` (see `Set.HasDensity.hasLogDensity`), but the converse
is false.
-/
def Set.HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / .log n : ℝ)) atTop (𝓝 d)

/-- If a set has natural density `d`, then it also has logarithmic density `d`. -/
theorem Set.HasDensity.hasLogDensity {A : Set ℕ} {d : ℝ} (h : A.HasDensity d) :
    A.HasLogDensity d := by
  classical
  rw [Set.HasLogDensity]
  let a : ℕ → ℝ := fun k => if k ∈ A then 1 else 0
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 n, a k
  let B : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / ((k : ℝ) + 1)
  have ha_nonneg : ∀ k, 0 ≤ a k := fun k => by
    by_cases hk : k ∈ A <;> simp [a, hk]
  have ha_le_one : ∀ k, a k ≤ 1 := fun k => by
    by_cases hk : k ∈ A <;> simp [a, hk]
  have hS_bound : ∀ n ≥ 1, |S n / (n : ℝ)| ≤ 1 := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hS_nonneg : 0 ≤ S n := Finset.sum_nonneg fun k _ => ha_nonneg k
    have hS_le : S n ≤ (n : ℝ) := by
      calc S n ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun k _ => ha_le_one k
        _ = (n : ℝ) := by simp
    rw [abs_of_nonneg (div_nonneg hS_nonneg hn_pos.le), div_le_one hn_pos]
    exact hS_le
  have hsum_eq : ∀ n : ℕ,
      (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / Real.log n) =
        (∑ k ∈ Finset.Icc 1 n, a k / (k : ℝ)) / Real.log n := by
    intro n
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_filter]
    have hIic : Finset.Iic n = insert 0 (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hIic, Finset.sum_insert (by simp)]
    simp only [Nat.cast_zero, inv_zero, ite_self, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ A <;> simp [a, hk, div_eq_mul_inv]
  have hpart : ∀ n : ℕ, A.partialDensity Set.univ (n + 1) = (a 0 + S n) / ((n : ℝ) + 1) := by
    intro n
    have hset :
        A ∩ Set.Iio (n + 1) = (((Finset.range (n + 1)).filter (· ∈ A) : Finset ℕ) : Set ℕ) := by
      ext k
      simp [Set.mem_Iio, and_comm]
    have hncard : ((A ∩ Set.Iio (n + 1)).ncard : ℝ) = a 0 + S n := by
      rw [hset, Set.ncard_coe_finset, Finset.card_filter, Nat.cast_sum]
      have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hrange, Finset.sum_insert (by simp)]
      congr 1
      · by_cases h0 : 0 ∈ A <;> simp [a, h0]
      · refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k ∈ A <;> simp [a, hk]
    simp [Set.partialDensity, hncard]
  have hS_tendsto : Tendsto (fun n : ℕ => S n / (n : ℝ)) atTop (𝓝 d) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
      have h1' : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) := by
        simpa using Tendsto.const_add (1 : ℝ) tendsto_one_div_atTop_nhds_zero_nat
      refine h1'.congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    have h2 : Tendsto (fun n : ℕ => A.partialDensity Set.univ (n + 1)) atTop (𝓝 d) :=
      h.comp (tendsto_add_atTop_nat 1)
    have h3 : Tendsto (fun n : ℕ => a 0 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (a 0)
    have hcomb : Tendsto
        (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ)) * A.partialDensity Set.univ (n + 1) -
          a 0 / (n : ℝ)) atTop (𝓝 d) := by
      simpa using (h1.mul h2).sub h3
    refine hcomb.congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
    rw [hpart n]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hIcc_succ : ∀ r : ℕ, Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
    intro r; ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : ∀ r : ℕ, r + 1 ∉ Finset.Icc 1 r := by
    intro r; simp
  have habel : ∀ m : ℕ,
      ∑ k ∈ Finset.Icc 1 (m + 1), a k / (k : ℝ) =
        S (m + 1) / ((m + 1 : ℕ) : ℝ) +
          ∑ k ∈ Finset.Icc 1 m, (S k / (k : ℝ)) / ((k : ℝ) + 1) := by
    intro m
    induction m with
    | zero =>
      simp [S]
    | succ m ih =>
      have hS_succ : S (m + 2) = S (m + 1) + a (m + 2) := by
        dsimp only [S]
        rw [hIcc_succ (m + 1), Finset.sum_insert (hnotmem (m + 1)), add_comm]
      rw [hIcc_succ (m + 1), Finset.sum_insert (hnotmem (m + 1)), add_comm, ih,
        hIcc_succ m, Finset.sum_insert (hnotmem m), hS_succ]
      push_cast
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
      have hm11 : (m : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
  have hH_upper : ∀ m : ℕ,
      ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((k : ℝ) + 1) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hIcc_succ m, Finset.sum_insert (hnotmem m)]
      have hstep : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ≤
          Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
        have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) := by positivity
        have hlog := Real.log_le_sub_one_of_pos hpos
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        have halg : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 =
            -((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) := by
          push_cast
          field_simp
          ring
        linarith
      linarith
  have hH_lower : ∀ m : ℕ,
      Real.log ((m + 2 : ℕ) : ℝ) - Real.log 2 ≤
        ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((k : ℝ) + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hIcc_succ m, Finset.sum_insert (hnotmem m)]
      have hstep : Real.log ((m + 3 : ℕ) : ℝ) - Real.log ((m + 2 : ℕ) : ℝ) ≤
          (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) := by
        have hpos : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) := by positivity
        have hlog := Real.log_le_sub_one_of_pos hpos
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        have halg : ((m + 3 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 =
            (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          field_simp
          ring
        linarith
      linarith
  have hB_le : ∀ n ≥ 1, B n ≤ Real.log (n : ℝ) := by
    intro n hn
    have hm : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [B, hm] using hH_upper (n - 1)
  have hB_err : ∀ n ≥ 1, |B n - Real.log (n : ℝ)| ≤ Real.log 2 := by
    intro n hn
    have hm2 : n - 1 + 2 = n + 1 := by omega
    have hlow1 : Real.log ((n + 1 : ℕ) : ℝ) - Real.log 2 ≤ B n := by
      simpa [B, hm2] using hH_lower (n - 1)
    have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.le_succ n)
    have hup : B n ≤ Real.log (n : ℝ) := hB_le n hn
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hS_tendsto (ε / 2) (half_pos hε)
  let N : ℕ := max N₀ 1
  have hN1 : 1 ≤ N := le_max_right N₀ 1
  have hN : ∀ k ≥ N, |S k / (k : ℝ) - d| < ε / 2 := fun k hk => by
    simpa [Real.dist_eq] using hN₀ k (le_trans (le_max_left N₀ 1) hk)
  let C : ℝ :=
    1 + |∑ k ∈ Finset.Icc 1 (N - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1)| + |d| * Real.log 2
  let R : ℝ := max 1 (2 * C / ε)
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp R)
  refine ⟨max (N + 1) M, fun n hn => ?_⟩
  rw [Real.dist_eq, hsum_eq n]
  have hnN : N + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have hR_lt : R < Real.log (n : ℝ) := by
    calc R = Real.log (Real.exp R) := (Real.log_exp R).symm
      _ < Real.log (n : ℝ) :=
        Real.log_lt_log (Real.exp_pos R) (hM.trans_le (Nat.cast_le.mpr hnM))
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    linarith [le_max_left 1 (2 * C / ε)]
  have hdiff :
      (∑ k ∈ Finset.Icc 1 n, a k / (k : ℝ)) / Real.log n - d =
        (S n / (n : ℝ) +
          ∑ k ∈ Finset.Icc 1 (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1) +
          d * (B n - Real.log n)) / Real.log n := by
    have hm : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hab := habel (n - 1)
    rw [hm] at hab
    rw [hab]
    have hsum_sub :
        ∑ k ∈ Finset.Icc 1 (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1) =
          (∑ k ∈ Finset.Icc 1 (n - 1), (S k / (k : ℝ)) / ((k : ℝ) + 1)) - d * B n := by
      simp_rw [sub_div, Finset.sum_sub_distrib, B, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum_sub]
    have hlog_ne : Real.log n ≠ 0 := hlog_pos.ne'
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos hlog_pos]
  have hsplit : Finset.Icc 1 (n - 1) = Finset.Icc 1 (N - 1) ∪ Finset.Icc N (n - 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (N - 1)) (Finset.Icc N (n - 1)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  have htail :
      |∑ k ∈ Finset.Icc N (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1)| ≤
        (ε / 2) * Real.log n := by
    calc |∑ k ∈ Finset.Icc N (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1)|
        ≤ ∑ k ∈ Finset.Icc N (n - 1), |(S k / (k : ℝ) - d) / ((k : ℝ) + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc N (n - 1), (ε / 2) * ((1 : ℝ) / ((k : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkN : N ≤ k := (Finset.mem_Icc.mp hk).1
          have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          rw [abs_div, abs_of_pos hpos, mul_one_div]
          exact div_le_div_of_nonneg_right (hN k hkN).le hpos.le
      _ = (ε / 2) * ∑ k ∈ Finset.Icc N (n - 1), (1 : ℝ) / ((k : ℝ) + 1) := by
          rw [← Finset.mul_sum]
      _ ≤ (ε / 2) * B n := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          simp only [Finset.mem_Icc] at hk ⊢
          omega
      _ ≤ (ε / 2) * Real.log n :=
          mul_le_mul_of_nonneg_left (hB_le n (by omega)) (by linarith)
  have hnum :
      |S n / (n : ℝ) +
          ∑ k ∈ Finset.Icc 1 (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1) +
          d * (B n - Real.log n)| ≤
        C + (ε / 2) * Real.log n := by
    rw [hsplit, Finset.sum_union hdisj]
    have h1 := abs_add_le
      (S n / (n : ℝ) +
        (∑ k ∈ Finset.Icc 1 (N - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1) +
          ∑ k ∈ Finset.Icc N (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1)))
      (d * (B n - Real.log n))
    have h2 := abs_add_le
      (S n / (n : ℝ))
      (∑ k ∈ Finset.Icc 1 (N - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1) +
        ∑ k ∈ Finset.Icc N (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1))
    have h3 := abs_add_le
      (∑ k ∈ Finset.Icc 1 (N - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1))
      (∑ k ∈ Finset.Icc N (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1))
    have hS1 : |S n / (n : ℝ)| ≤ 1 := hS_bound n (by omega)
    have hd_err : |d * (B n - Real.log n)| ≤ |d| * Real.log 2 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB_err n (by omega)) (abs_nonneg d)
    dsimp only [C]
    linarith
  have hC_div : C / Real.log n < ε / 2 := by
    rw [div_lt_div_iff₀ hlog_pos (by norm_num : (0 : ℝ) < 2)]
    have h2C : 2 * C / ε < Real.log n := (le_max_right 1 (2 * C / ε)).trans_lt hR_lt
    rw [div_lt_iff₀ hε] at h2C
    linarith
  calc |S n / (n : ℝ) +
        ∑ k ∈ Finset.Icc 1 (n - 1), (S k / (k : ℝ) - d) / ((k : ℝ) + 1) +
        d * (B n - Real.log n)| / Real.log n
      ≤ (C + (ε / 2) * Real.log n) / Real.log n :=
        div_le_div_of_nonneg_right hnum hlog_pos.le
    _ = C / Real.log n + ε / 2 := by
        rw [add_div, mul_div_cancel_right₀ _ hlog_pos.ne']
    _ < ε := by linarith

end LogarithmicDensity
