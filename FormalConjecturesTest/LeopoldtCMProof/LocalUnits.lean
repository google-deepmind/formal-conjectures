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

public import Mathlib
public import FormalConjecturesForMathlib.Leopoldt.NumberTheory.Padics.OneUnits
public import FormalConjecturesTest.LeopoldtCMProof.ResidueField

/-!
# Local units at a prime of a number field

Let `K` be a number field, `v` a prime of `𝓞 K`, `K_v` its completion and `𝓞_v` the valuation
ring of `K_v`. This file relates the principal units `oneUnits K_v = {u : ‖u - 1‖ < 1}` of
`FormalConjecturesForMathlib.Leopoldt.NumberTheory.Padics.OneUnits` to the unit group `𝓞_vˣ`,
and proves the facts about them that the comparison of Mihăilescu's `p`-adic closure
`⋂ₙ ι(E) · U^{pⁿ}` with the topological closure of `E₁` in `U₁` needs.

## Main definitions

* `toIntegerUnits v : oneUnits K_v →* 𝓞_vˣ`: the inclusion of the principal units of `K_v`
  into the units of `𝓞_v`.

## Main results

* `mem_range_toIntegerUnits_iff`: the range of `toIntegerUnits` is the set of units of `𝓞_v`
  that are congruent to `1` modulo `𝔪_v`.
* `oneUnits_eq_principalUnitGroup`: `oneUnits K_v` is Mathlib's
  `ValuationSubring.principalUnitGroup` of `𝓞_v`, which is what `toIntegerUnits` and
  `mem_range_toIntegerUnits_iff_residue` are built from.
* `residue_eq_one_iff_valued_sub_one_lt`: an element of `𝓞_v` has residue `1` exactly when it
  is congruent to `1` modulo `𝔪_v`.
* `exists_forall_pow_pow_mem_nhds_one`: when `‖n‖ < 1`, the `nᵏ`-th powers of *all* principal
  units eventually lie in any given neighbourhood of `1` — the convergence is uniform in the
  unit, which pointwise pro-`p` convergence does not give. This rests on the contraction
  estimate `‖u ^ n - 1‖ ≤ ‖u - 1‖ · max ‖u - 1‖ ‖n‖` (`norm_pow_sub_one_le_mul_max`) and on
  the norm of `K_v` being discrete (`exists_lt_one_forall_norm_le`).
* `PadicInt.exists_eq_appr_add_pow_mul`: the decomposition `a = a.appr n + pⁿ c` of a `p`-adic
  integer, used to split a `p`-adic power into an integer power and a `pⁿ`-th power.

The contraction estimates hold in any ultrametric normed field and need no completeness.
-/

@[expose] public section

open Filter IsDedekindDomain NumberField Topology

open scoped NumberField Valued WithZero

/-- `a = a.appr n + pⁿ c` for some `c ∈ ℤ_p`: the `n`-th integer approximation of `a` is exact
modulo `pⁿ` (`PadicInt.appr_spec`). -/
theorem PadicInt.exists_eq_appr_add_pow_mul {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (n : ℕ) :
    ∃ c : ℤ_[p], a = a.appr n + (p : ℤ_[p]) ^ n * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
  exact ⟨c, by linear_combination hc⟩

namespace Leopoldt

section Contraction

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

/-- `u ^ n - 1 = (u - 1) (u ^ (n - 1) + ⋯ + 1)`, and the second factor is `n` plus a sum of terms
`u ^ j - 1` of norm at most `‖u - 1‖`. -/
theorem norm_pow_sub_one_le_mul_max (n : ℕ) {u : L} (hu : ‖u - 1‖ ≤ 1) :
    ‖u ^ n - 1‖ ≤ ‖u - 1‖ * max ‖u - 1‖ ‖(n : L)‖ := by
  have hu1 : ‖u‖ ≤ 1 := by
    rw [← sub_add_cancel u 1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu (by simp))
  have hgeom : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = u ^ n - 1 := by
    simpa using (Commute.one_right u).geom_sum₂_mul n
  have hsum : (∑ i ∈ Finset.range n, (u ^ i - 1)) + (n : L) = ∑ i ∈ Finset.range n, u ^ i := by
    rw [Finset.sum_sub_distrib]
    simp
  calc ‖u ^ n - 1‖ = ‖(∑ i ∈ Finset.range n, (u ^ i - 1)) + (n : L)‖ * ‖u - 1‖ := by
        rw [← norm_mul, hsum, hgeom]
    _ ≤ max ‖u - 1‖ ‖(n : L)‖ * ‖u - 1‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
          fun i _ ↦ OneUnits.norm_pow_sub_one_le hu1 i
    _ = ‖u - 1‖ * max ‖u - 1‖ ‖(n : L)‖ := mul_comm _ _

/-- Iterating `norm_pow_sub_one_le_mul_max`: on the ball `‖u - 1‖ ≤ c ≤ 1` the `n ^ k`-th power
map contracts towards `1` by the factor `max c ‖n‖` at each step. -/
theorem norm_pow_pow_sub_one_le (n k : ℕ) {c : ℝ} (hc : c ≤ 1) {u : L} (hu : ‖u - 1‖ ≤ c) :
    ‖u ^ n ^ k - 1‖ ≤ max c ‖(n : L)‖ ^ k * c := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hu
  have hlam : max c ‖(n : L)‖ ≤ 1 := max_le hc (IsUltrametricDist.norm_natCast_le_one L n)
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    have hle : max c ‖(n : L)‖ ^ k * c ≤ c :=
      mul_le_of_le_one_left hc0 (pow_le_one₀ (le_max_of_le_left hc0) hlam)
    calc ‖u ^ n ^ (k + 1) - 1‖ = ‖(u ^ n ^ k) ^ n - 1‖ := by rw [pow_succ, pow_mul]
      _ ≤ ‖u ^ n ^ k - 1‖ * max ‖u ^ n ^ k - 1‖ ‖(n : L)‖ :=
          norm_pow_sub_one_le_mul_max n (ih.trans (hle.trans hc))
      _ ≤ max c ‖(n : L)‖ ^ k * c * max c ‖(n : L)‖ :=
          mul_le_mul ih (max_le_max (ih.trans hle) le_rfl)
            (le_max_of_le_left (norm_nonneg _)) (by positivity)
      _ = max c ‖(n : L)‖ ^ (k + 1) * c := by ring

end Contraction

section AdicCompletion

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The norm of `K_v` is discrete: there is `c < 1` such that `‖x‖ < 1` implies `‖x‖ ≤ c`. One
can take `c = ‖π‖` for a uniformiser `π`. -/
theorem exists_lt_one_forall_norm_le :
    ∃ c : ℝ, c < 1 ∧ ∀ x : v.adicCompletion K, ‖x‖ < 1 → ‖x‖ ≤ c := by
  obtain ⟨π, hπ⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-1 : ℤ))
  have key : ∀ y : ℤᵐ⁰, y < 1 → y ≤ WithZero.exp (-1 : ℤ) := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_le
    · rw [← WithZero.log_le_iff_le_exp hy0]
      have h := (WithZero.log_lt_iff_lt_exp hy0 (a := 0)).2 (by simpa using hy)
      lia
  refine ⟨‖π‖, ?_, fun x hx ↦ ?_⟩
  · refine Valued.toNormedField.norm_lt_one_iff.2 ?_
    rw [hπ]
    simpa using WithZero.exp_lt_exp.2 (neg_one_lt_zero (R := ℤ))
  · refine Valued.toNormedField.norm_le_iff.2 ?_
    rw [hπ]
    exact key _ (Valued.toNormedField.norm_lt_one_iff.1 hx)

/-- If `‖n‖ < 1` in `K_v`, the `n ^ k`-th powers of the principal units tend to `1` uniformly:
for every `ε > 0` there is `k₀` with `‖x ^ n ^ k - 1‖ < ε` for all `k ≥ k₀` and all `x` with
`‖x - 1‖ < 1`. -/
theorem exists_forall_norm_pow_pow_sub_one_lt {n : ℕ} (hn : ‖(n : v.adicCompletion K)‖ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ x : v.adicCompletion K, ‖x - 1‖ < 1 → ‖x ^ n ^ k - 1‖ < ε := by
  obtain ⟨c, hc1, hc⟩ := exists_lt_one_forall_norm_le v
  have hten : Tendsto (fun k : ℕ ↦ max c ‖(n : v.adicCompletion K)‖ ^ k * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_of_le_right (norm_nonneg _))
      (max_lt hc1 hn)).mul_const c
  obtain ⟨k₀, hk₀⟩ := (hten.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  exact ⟨k₀, fun k hk x hx ↦
    (norm_pow_pow_sub_one_le n k hc1.le (hc _ hx)).trans_lt (hk₀ k hk)⟩

/-- Topological form of `exists_forall_norm_pow_pow_sub_one_lt`: for every neighbourhood `s` of
`1` in `K_v`, the `n ^ k`-th powers of *all* principal units eventually lie in `s`. -/
theorem exists_forall_pow_pow_mem_nhds_one {n : ℕ} (hn : ‖(n : v.adicCompletion K)‖ < 1)
    {s : Set (v.adicCompletion K)} (hs : s ∈ 𝓝 (1 : v.adicCompletion K)) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ x : v.adicCompletion K, ‖x - 1‖ < 1 → x ^ n ^ k ∈ s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨k₀, hk₀⟩ := exists_forall_norm_pow_pow_sub_one_lt v hn hδ
  exact ⟨k₀, fun k hk x hx ↦ hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hk₀ k hk x hx)⟩

/-- The principal units of `K_v` are exactly Mathlib's `ValuationSubring.principalUnitGroup` of
`𝓞_v`. The two definitions differ only in whether the condition `x ≡ 1` is expressed with the
norm (as `oneUnits` does) or with the valuation subring's own valuation, and those agree by
`Valuation.isEquiv_valuation_valuationSubring`. Rewriting along this makes all of Mathlib's
principal-unit API available for `oneUnits (v.adicCompletion K)`. -/
theorem oneUnits_eq_principalUnitGroup :
    oneUnits (v.adicCompletion K) = (v.adicCompletionIntegers K).principalUnitGroup := by
  ext u
  rw [OneUnits.mem_oneUnits_iff, Valued.toNormedField.norm_lt_one_iff,
    ValuationSubring.mem_principalUnitGroup_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).lt_one_iff_lt_one

/-- An element of `𝓞_v` has residue `1` exactly when it is congruent to `1` modulo `𝔪_v`.
Stated with `Valued.v` rather than `‖·‖`: the completion carries two definitionally equal but
syntactically different norm instances (`Valued.toNormedField` and
`NumberField.instNormedFieldValuedAdicCompletion`), and matching them across files is expensive,
whereas the valuation is unique. -/
theorem residue_eq_one_iff_valued_sub_one_lt {x : v.adicCompletionIntegers K} :
    IsLocalRing.residue (v.adicCompletionIntegers K) x = 1 ↔
      Valued.v ((x : v.adicCompletion K) - 1) < 1 := by
  rw [← map_one (IsLocalRing.residue (v.adicCompletionIntegers K)), ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff,
    HeightOneSpectrum.mem_maximalIdeal_adicCompletionIntegers_iff, AddSubgroupClass.coe_sub,
    OneMemClass.coe_one]

/-- The inclusion of the principal units of `K_v` into the units of `𝓞_v`. Through
`oneUnits_eq_principalUnitGroup` this is Mathlib's `ValuationSubring.principalUnitGroupEquiv`,
which identifies the principal units with the kernel of the residue map `𝓞_vˣ → k_vˣ`; that is
what makes `mem_range_toIntegerUnits_iff_residue` immediate. -/
noncomputable def toIntegerUnits :
    oneUnits (v.adicCompletion K) →* (v.adicCompletionIntegers K)ˣ :=
  ((Units.map (IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom).ker.subtype).comp
    ((v.adicCompletionIntegers K).principalUnitGroupEquiv.toMonoidHom.comp
      (Subgroup.inclusion (oneUnits_eq_principalUnitGroup v).le))

/-- `toIntegerUnits` does not move the underlying element of `K_v`; it only repackages a unit
of `K_v` as a unit of `𝓞_v`. This is the `rfl`-lemma that lets the two coercion towers
(`oneUnits K_v → K_vˣ → K_v` and `𝓞_vˣ → 𝓞_v → K_v`) be compared. -/
theorem coe_toIntegerUnits_apply (u : oneUnits (v.adicCompletion K)) :
    ((toIntegerUnits v u : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((u : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
  ValuationSubring.principalUnitGroupEquiv_apply _ _

/-- `toIntegerUnits v` is injective, being a subgroup inclusion followed by an equivalence. -/
theorem toIntegerUnits_injective : Function.Injective (toIntegerUnits v) :=
  (Subgroup.subtype_injective _).comp
    ((v.adicCompletionIntegers K).principalUnitGroupEquiv.injective.comp
      (Subgroup.inclusion_injective _))

/-- `toIntegerUnits v` is continuous. Both unit groups carry the topology induced from
`K_v × K_vᵐᵒᵖ`, so `Units.continuous_iff` reduces this to continuity of `u ↦ u` and
`u ↦ u⁻¹` into `K_v`. Mathlib's `principalUnitGroupEquiv` is purely algebraic, so this is the
one part of the interface that has to be proved here. -/
theorem continuous_toIntegerUnits : Continuous (toIntegerUnits v) := by
  have hinv : ∀ u : oneUnits (v.adicCompletion K),
      ((((toIntegerUnits v u)⁻¹ : (v.adicCompletionIntegers K)ˣ) :
          v.adicCompletionIntegers K) : v.adicCompletion K)
        = (((u : (v.adicCompletion K)ˣ)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    intro u
    rw [← map_inv, coe_toIntegerUnits_apply, Subgroup.coe_inv]
  refine Units.continuous_iff.2 ⟨continuous_induced_rng.2 ?_, continuous_induced_rng.2 ?_⟩
  · simp only [Function.comp_def, coe_toIntegerUnits_apply]
    exact Units.continuous_val.comp continuous_subtype_val
  · simp only [Function.comp_def, hinv]
    exact Units.continuous_coe_inv.comp continuous_subtype_val

/-- The range of `toIntegerUnits` is the kernel of the residue map `𝓞_vˣ → k_vˣ`: a unit of
`𝓞_v` is a principal unit exactly when its residue is `1`. This is
`ValuationSubring.principalUnitGroupEquiv` read as a statement about the range. -/
theorem mem_range_toIntegerUnits_iff_residue (w : (v.adicCompletionIntegers K)ˣ) :
    w ∈ (toIntegerUnits v).range ↔
      Units.map (IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom w = 1 := by
  rw [MonoidHom.mem_range, ← MonoidHom.mem_ker]
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact ((v.adicCompletionIntegers K).principalUnitGroupEquiv
      (Subgroup.inclusion (oneUnits_eq_principalUnitGroup v).le u)).2
  · refine ⟨⟨(((v.adicCompletionIntegers K).principalUnitGroupEquiv.symm ⟨w, hw⟩ :
      (v.adicCompletion K)ˣ)), ?_⟩, Units.ext (Subtype.ext ?_)⟩
    · rw [oneUnits_eq_principalUnitGroup]
      exact ((v.adicCompletionIntegers K).principalUnitGroupEquiv.symm ⟨w, hw⟩).2
    · rw [coe_toIntegerUnits_apply]
      exact ValuationSubring.principalUnitGroup_symm_apply _ _

/-- The range of `toIntegerUnits` consists of the units `w` of `𝓞_v` with `w ≡ 1` modulo
`𝔪_v`. -/
theorem mem_range_toIntegerUnits_iff (w : (v.adicCompletionIntegers K)ˣ) :
    w ∈ (toIntegerUnits v).range ↔
      Valued.v (((w : v.adicCompletionIntegers K) : v.adicCompletion K) - 1) < 1 := by
  rw [mem_range_toIntegerUnits_iff_residue, Units.ext_iff, Units.coe_map, Units.val_one]
  exact residue_eq_one_iff_valued_sub_one_lt v

end AdicCompletion

end Leopoldt
