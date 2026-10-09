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
public import Batteries.Util.ProofWanted
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

/-- The number of multiples of `k ≥ 1` below `n ≥ 1` is `⌈n / k⌉ = (n + k - 1) / k`. -/
theorem ncard_multiples_Iio {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ({m : ℕ | k ∣ m} ∩ Iio n).ncard = (n + k - 1) / k := by
  have hkpos : 0 < k := hk
  have : {m : ℕ | k ∣ m} ∩ Iio n = (fun j => j * k) '' Iio ((n + k - 1) / k) := by
    ext m
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Iio, mem_image]
    constructor
    · rintro ⟨⟨j, rfl⟩, hm⟩
      refine ⟨j, ?_, mul_comm _ _⟩
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hkpos]
      rw [mul_comm k j] at hm
      rw [add_mul]
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j, mul_comm _ _⟩, ?_⟩
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hkpos, add_mul] at hj
      omega
  rw [this, ncard_image_of_injective _ (mul_left_injective₀ (by omega)), ncard_Iio]

/-- The set of multiples of a positive integer `k` has natural density `1 / k`. -/
theorem hasDensity_multiples {k : ℕ} (hk : 1 ≤ k) : {n : ℕ | k ∣ n}.HasDensity (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio]
  have hlow : ∀ n : ℕ, 1 ≤ n → 1 / (k : ℝ) ≤ (({n : ℕ | k ∣ n} ∩ Iio n).ncard : ℝ) / n := by
    intro n hn
    rw [ncard_multiples_Iio hk hn]
    have h1 : n ≤ k * ((n + k - 1) / k) := by
      have := Nat.lt_mul_div_succ (n + k - 1) (show 0 < k from hk)
      rw [mul_add, mul_one] at this
      omega
    have h2 : (n : ℝ) ≤ k * (((n + k - 1) / k : ℕ) : ℝ) := by exact_mod_cast h1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ hkR hnR]
    linarith
  have hup : ∀ n : ℕ, 1 ≤ n →
      (({n : ℕ | k ∣ n} ∩ Iio n).ncard : ℝ) / n ≤ 1 / (k : ℝ) + 1 / n := by
    intro n hn
    rw [ncard_multiples_Iio hk hn]
    have h1 : k * ((n + k - 1) / k) ≤ n + k - 1 := Nat.mul_div_le _ _
    have h2 : (k : ℝ) * (((n + k - 1) / k : ℕ) : ℝ) ≤ n + k := by
      have : k * ((n + k - 1) / k) ≤ n + k := by omega
      exact_mod_cast this
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_add_div _ _ hkR.ne' hnR.ne', div_le_div_iff₀ hnR (by positivity)]
    nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (eventually_atTop.2 ⟨1, hlow⟩) (eventually_atTop.2 ⟨1, hup⟩)
  simpa using Tendsto.const_add (1 / (k : ℝ)) tendsto_one_div_atTop_nhds_zero_nat

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
proof_wanted Set.HasDensity.hasLogDensity {A : Set ℕ} {d : ℝ} (h : A.HasDensity d) : A.HasLogDensity d

end LogarithmicDensity
