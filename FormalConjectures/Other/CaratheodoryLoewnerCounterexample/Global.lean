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

import FormalConjecturesUtil
import FormalConjecturesForMathlib.Analysis.SpecialFunctions.FlatRpowExp
import FormalConjecturesForMathlib.Geometry.SupportFunctionSphere
import FormalConjectures.Other.CaratheodoryLoewnerCounterexample.Smooth
import FormalConjectures.Other.CaratheodoryLoewnerCounterexample.Index
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The global smooth Carathéodory counterexample

This file extends `counterexample 2` across the sphere and realizes it as the support function of
a smooth strictly convex body with a unique umbilic.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open scoped ContDiff EuclideanGeometry Manifold
open Set Metric

namespace CaratheodoryLoewnerCounterexample

open CaratheodoryConjecture LoewnerConjecture

private local instance : Fact (Module.finrank ℝ ℝ³ = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The complex coordinate inverse to `counterexampleSphereChart` away from the north pole. -/
private noncomputable def counterexampleSphereCoord
    (p : sphere (0 : ℝ³) 1) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm
    ((2 : ℝ)⁻¹ • (stereographic' 2 counterexampleNorthPole) p)

/-- The chosen complex coordinate is a left inverse to the spherical chart. -/
@[category API, AMS 53]
private theorem counterexampleSphereCoord_chart (z : ℂ) :
    counterexampleSphereCoord (counterexampleSphereChart z) = z := by
  apply Complex.ext <;> simp [counterexampleSphereCoord, counterexampleSphereChart]

/-- Away from the north pole, the spherical chart is also a left inverse to its chosen complex
coordinate. -/
@[category API, AMS 53]
private theorem counterexampleSphereChart_coord {p : sphere (0 : ℝ³) 1}
    (hp : p ≠ counterexampleNorthPole) :
    counterexampleSphereChart (counterexampleSphereCoord p) = p := by
  have hp_source : p ∈ (stereographic' 2 counterexampleNorthPole).source := by
    simpa [stereographic'_source] using hp
  rw [counterexampleSphereChart, counterexampleSphereCoord,
    ← (stereographic' 2 counterexampleNorthPole).left_inv hp_source]
  congr 1
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  apply Complex.ext <;> simp

/-- The inverse complex coordinate is smooth on the complement of its projection pole. -/
@[category API, AMS 53]
private theorem counterexampleSphereCoord_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ counterexampleSphereCoord
      {counterexampleNorthPole}ᶜ := by
  let e := stereographic' 2 counterexampleNorthPole
  have he : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ (sphere (0 : ℝ³) 1) :=
    IsManifold.subset_maximalAtlas ⟨counterexampleNorthPole, rfl⟩
  have hcoord : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 2) ↦
        Complex.orthonormalBasisOneI.repr.symm ((2 : ℝ)⁻¹ • x)) :=
    Complex.orthonormalBasisOneI.repr.symm.contDiff.comp
      (contDiff_const_smul (𝕜 := ℝ) (2 : ℝ)⁻¹)
  rw [← stereographic'_source (n := 2) counterexampleNorthPole]
  exact hcoord.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas he)

/-- The pointwise extension of `counterexample 2` obtained by assigning its limiting value at the
north pole. Smoothness at that point is the substantive content of the extension theorem. -/
private noncomputable def counterexampleTwoSphereExtension
    (p : sphere (0 : ℝ³) 1) : ℝ :=
  if p = counterexampleNorthPole then 10 ^ 10 + 3 / 160
  else counterexample 2 (counterexampleSphereCoord p)

/-- The pointwise spherical extension agrees with the announced formula in its finite chart. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_chart (z : ℂ) :
    counterexampleTwoSphereExtension (counterexampleSphereChart z) = counterexample 2 z := by
  have hmem : counterexampleSphereChart z ∈
      (stereographic' 2 counterexampleNorthPole).source := by
    simpa [counterexampleSphereChart] using
      (stereographic' 2 counterexampleNorthPole).map_target
        (show 2 • Complex.orthonormalBasisOneI.repr z ∈
          (stereographic' 2 counterexampleNorthPole).target by simp)
  have hne : counterexampleSphereChart z ≠ counterexampleNorthPole := by
    simpa [stereographic'_source] using hmem
  simp [counterexampleTwoSphereExtension, hne, counterexampleSphereCoord_chart]

/-- The pointwise extension is smooth away from the north pole. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension
      {counterexampleNorthPole}ᶜ := by
  have hcounterexample : ContDiff ℝ ∞ (counterexample 2) :=
    counterexample_contDiff 2 (by omega)
  refine (hcounterexample.contMDiff.comp_contMDiffOn
    counterexampleSphereCoord_contMDiffOn).congr ?_
  intro p hp
  have hpne : p ≠ counterexampleNorthPole := by simpa using hp
  simp [counterexampleTwoSphereExtension, hpne]

/-- Smoothness at the north pole is the only missing local condition for smoothness of the
pointwise extension on the whole sphere. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
    (hnorth : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension
      counterexampleNorthPole) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension := by
  intro p
  by_cases hp : p = counterexampleNorthPole
  · simpa [hp] using hnorth
  · exact (counterexampleTwoSphereExtension_contMDiffOn p (by simpa)).contMDiffAt
      (isOpen_compl_singleton.mem_nhds (by simpa))

/-- The flat scalar appearing in the reciprocal chart at the north pole. On the nonnegative
half-line this is `(s / 10000) ^ (1 / 8) * exp (-10000 / s)`. -/
private noncomputable def counterexampleTwoReciprocalExponent (s : ℝ) : ℝ :=
  (10000 : ℝ) ^ (-(1 : ℝ) / 8) *
    (s ^ ((1 : ℝ) / 8) * Real.flatRpowExp 1 10000 s)

/-- The reciprocal-chart exponent is smooth across `s = 0`. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocalExponent := by
  exact contDiff_const.mul
    (Real.flatRpowExp.rpow_mul_contDiff (by norm_num) (by norm_num) ((1 : ℝ) / 8))

/-- On the positive half-line, the smooth flat extension has the reciprocal-chart formula from
the informal calculation. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_of_pos {s : ℝ} (hs : 0 < s) :
    counterexampleTwoReciprocalExponent s =
      (s / 10000) ^ ((1 : ℝ) / 8) * Real.exp (-10000 / s) := by
  rw [counterexampleTwoReciprocalExponent, Real.flatRpowExp.of_pos 1 10000 hs]
  have hscale :
      (10000 : ℝ) ^ (-(1 : ℝ) / 8) * s ^ ((1 : ℝ) / 8) =
        (s / 10000) ^ ((1 : ℝ) / 8) := by
    rw [show -(1 : ℝ) / 8 = -((1 : ℝ) / 8) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10000), Real.div_rpow hs.le
      (by norm_num : (0 : ℝ) ≤ 10000)]
    field_simp
  rw [← mul_assoc, hscale]
  congr 2
  field_simp [hs.ne']
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hs.ne']

/-- The positive radial coefficient multiplying the seed in the reciprocal chart. -/
private noncomputable def counterexampleTwoReciprocalDamping (w : ℂ) : ℝ :=
  let s := ‖w‖ ^ 2
  10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)

/-- The reciprocal-chart damping coefficient is smooth on the whole complex plane. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalDamping_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocalDamping := by
  have hs : ContDiff ℝ ∞ (fun w : ℂ ↦ ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  have hdenom : ∀ w : ℂ, ‖w‖ ^ 2 + 10000 ≠ 0 := by
    intro w
    positivity
  exact (contDiff_const.div (hs.add contDiff_const) hdenom).mul
    ((counterexampleTwoReciprocalExponent_contDiff.comp hs).neg.exp)

/-- Away from zero, the smooth damping coefficient has the explicit reciprocal-chart formula. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalDamping_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    counterexampleTwoReciprocalDamping w =
      10000 / (‖w‖ ^ 2 + 10000) *
        Real.exp (-((‖w‖ ^ 2 / 10000) ^ ((1 : ℝ) / 8) *
          Real.exp (-10000 / ‖w‖ ^ 2))) := by
  rw [counterexampleTwoReciprocalDamping,
    counterexampleTwoReciprocalExponent_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hw))]

/-- The smooth representative of `counterexample 2` in its reciprocal chart. -/
private noncomputable def counterexampleTwoReciprocal (w : ℂ) : ℝ :=
  10 ^ 10 + counterexampleTwoReciprocalDamping w * counterexampleSeed w

/-- The reciprocal representative is smooth, including at its origin. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocal_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocal := by
  exact contDiff_const.add
    (counterexampleTwoReciprocalDamping_contDiff.mul counterexampleSeed_contDiff)

/-- The reciprocal representative takes the limiting value used in the pointwise spherical
extension at its origin. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocal_zero :
    counterexampleTwoReciprocal 0 = 10 ^ 10 + 3 / 160 := by
  simp [counterexampleTwoReciprocal, counterexampleTwoReciprocalDamping,
    counterexampleTwoReciprocalExponent, counterexampleSeed]
  ring

/-- The reciprocal-star transformation used between the two complex charts is an involution. -/
@[category API, AMS 53]
private theorem hundred_div_star_involutive (w : ℂ) :
    (100 : ℂ) / star ((100 : ℂ) / star w) = w := by
  rw [star_div₀, star_star]
  norm_num

/-- The original finite-chart formula becomes the smooth reciprocal representative under
`z = 100 / star w`. -/
@[category API, AMS 53]
private theorem counterexample_two_reciprocal {w : ℂ} (hw : w ≠ 0) :
    counterexample 2 (100 / star w) = counterexampleTwoReciprocal w := by
  have hnorm : ‖(100 : ℂ) / star w‖ = 100 / ‖w‖ := by
    simp
  have hnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have harg := hundred_div_star_involutive w
  have hrpow :
      (100 / ‖w‖) ^ (-((1 : ℝ) / 4)) =
        (‖w‖ ^ 2 / 10000) ^ ((1 : ℝ) / 8) := by
    calc
      (100 / ‖w‖) ^ (-((1 : ℝ) / 4)) = (‖w‖ / 100) ^ ((1 : ℝ) / 4) := by
        rw [Real.rpow_neg_eq_inv_rpow]
        congr 2
        field_simp
      _ = ((‖w‖ / 100) ^ 2) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_natCast_mul (div_nonneg (norm_nonneg _) (by norm_num)) 2]
        norm_num
      _ = (‖w‖ ^ 2 / 10000) ^ ((1 : ℝ) / 8) := by
        congr 2
        ring
  have hsquare : -(100 / ‖w‖) ^ 2 = -10000 / ‖w‖ ^ 2 := by
    field_simp [hnorm_pos.ne']
    ring
  have hprefactor :
      (100 / ‖w‖) ^ 2 / (1 + (100 / ‖w‖) ^ 2) =
        10000 / (‖w‖ ^ 2 + 10000) := by
    field_simp [hnorm_pos.ne']
    ring
  rw [counterexample, counterexampleTwoReciprocal,
    counterexampleTwoReciprocalDamping_of_ne_zero hw]
  simp only [hnorm, harg]
  norm_num [Complex.cpow_one]
  rw [hrpow, hsquare, ← hprefactor]
  ring

/-- The real-linear reciprocal coordinate associated to the standard chart at the north pole.
The two orthonormal bases account for the fixed basis choice in mathlib's opposite
stereographic charts. -/
private noncomputable def counterexampleTwoReciprocalLinearCoord
    (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  let Upos := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  50 • Complex.orthonormalBasisOneI.repr.symm
    (Upos ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection
      (Uneg.symm x : ℝ³)))

/-- The fixed isometry from the complex reciprocal coordinate to the tangent plane at the
north pole. -/
private noncomputable def counterexampleTwoTangentEquiv :
    ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ :=
  Complex.orthonormalBasisOneI.repr.trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
      (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr.symm

/-- Ambient rational formula for the finite stereographic chart used in the statement. -/
@[category API, AMS 53]
private theorem counterexampleSphereChart_coe (z : ℂ) :
    (counterexampleSphereChart z : ℝ³) =
      (‖z‖ ^ 2 + 1)⁻¹ •
        (2 • (counterexampleTwoTangentEquiv z : ℝ³) +
          (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : ℝ³)) := by
  rw [counterexampleSphereChart, stereographic'_symm_apply]
  simp only [counterexampleTwoTangentEquiv, LinearIsometryEquiv.trans_apply,
    ← Nat.cast_smul_eq_nsmul ℝ 2, map_smul]
  simp only [Submodule.norm_coe, norm_smul, Real.norm_eq_abs,
    LinearIsometryEquiv.norm_map]
  have habs : |((2 : ℕ) : ℝ)| = 2 := by norm_num
  rw [habs]
  rw [show (2 * ‖z‖) ^ 2 = 4 * ‖z‖ ^ 2 by ring]
  simp only [Submodule.coe_smul, smul_add, smul_smul]
  have htangent : (4 * ‖z‖ ^ 2 + 4)⁻¹ * 4 * 2 =
      (‖z‖ ^ 2 + 1)⁻¹ * 2 := by field_simp
  have hpole : (4 * ‖z‖ ^ 2 + 4)⁻¹ * (4 * ‖z‖ ^ 2 - 4) =
      (‖z‖ ^ 2 + 1)⁻¹ * (‖z‖ ^ 2 - 1) := by field_simp
  norm_num only [Nat.cast_ofNat]
  rw [show (4 * ‖z‖ ^ 2 + 4)⁻¹ * 8 =
      (‖z‖ ^ 2 + 1)⁻¹ * 2 by
        calc
          _ = (4 * ‖z‖ ^ 2 + 4)⁻¹ * 4 * 2 := by ring
          _ = _ := htangent, hpole]

/-- At the south pole the finite chart differential is twice the fixed tangent-plane
isometry. -/
@[category API, AMS 53]
private theorem counterexampleSphereChart_fderiv_zero_apply (v : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 v =
      2 • (counterexampleTwoTangentEquiv v : ℝ³) := by
  have heq : (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) =
      fun z : ℂ ↦ (‖z‖ ^ 2 + 1)⁻¹ •
        (2 • (counterexampleTwoTangentEquiv z : ℝ³) +
          (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : ℝ³)) := by
    funext z
    exact counterexampleSphereChart_coe z
  rw [heq]
  let T : ℂ →L[ℝ] ℝ³ :=
    (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hT : HasFDerivAt (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³)) T 0 :=
    T.hasFDerivAt
  have hs : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2) (0 : ℂ →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt
  have hden : HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 + 1)⁻¹)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    convert (hasDerivAt_inv
      (by norm_num : ‖(0 : ℂ)‖ ^ 2 + (1 : ℝ) ≠ 0)).hasFDerivAt.comp 0
      (hs.add_const 1) using 1 ; ext x ; simp
  have hlinear : HasFDerivAt
      (fun z : ℂ ↦ 2 • (counterexampleTwoTangentEquiv z : ℝ³)) (T + T) 0 := by
    simpa only [two_smul] using hT.add hT
  have hradial : HasFDerivAt
      (fun z : ℂ ↦ (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : ℝ³))
      (0 : ℂ →L[ℝ] ℝ³) 0 := by
    convert (hs.sub_const 1).smul_const (counterexampleNorthPole : ℝ³) using 1 ;
      ext x ; simp
  have hnum : HasFDerivAt
      (fun z : ℂ ↦ 2 • (counterexampleTwoTangentEquiv z : ℝ³) +
        (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : ℝ³))
      (T + T) 0 := by
    simpa using hlinear.add hradial
  have hprod := hden.smul hnum
  change (fderiv ℝ (((fun z : ℂ ↦ (‖z‖ ^ 2 + 1)⁻¹) •
    fun z ↦ 2 • (counterexampleTwoTangentEquiv z : ℝ³) +
      (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : ℝ³))) 0) v = _
  rw [hprod.fderiv]
  simp [T, two_smul]

/-- The finite chart differential at the south pole has the whole tangent plane as its range. -/
@[category API, AMS 53]
private theorem range_fderiv_counterexampleSphereChart_zero :
    (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0).range =
      (ℝ ∙ (counterexampleSphereChart 0 : ℝ³))ᗮ := by
  rw [counterexampleSphereChart_zero]
  change (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0).range =
    (ℝ ∙ (-(counterexampleNorthPole : ℝ³)))ᗮ
  have hspan : ℝ ∙ (-(counterexampleNorthPole : ℝ³)) =
      ℝ ∙ (counterexampleNorthPole : ℝ³) := by
    rw [Submodule.span_singleton_eq_span_singleton]
    exact ⟨(-1 : ℝˣ), by simp⟩
  rw [hspan]
  apply le_antisymm
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    change fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 v ∈ _
    rw [counterexampleSphereChart_fderiv_zero_apply]
    simpa only [two_nsmul] using
      Submodule.add_mem _ (counterexampleTwoTangentEquiv v).2
        (counterexampleTwoTangentEquiv v).2
  · intro y hy
    let v : ℂ := counterexampleTwoTangentEquiv.symm ⟨y, hy⟩
    refine ⟨(2 : ℝ)⁻¹ • v, ?_⟩
    change fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0
      ((2 : ℝ)⁻¹ • v) = y
    rw [counterexampleSphereChart_fderiv_zero_apply]
    simp only [v, map_smul, LinearIsometryEquiv.apply_symm_apply, Submodule.coe_smul]
    change (2 : ℕ) • ((2 : ℝ)⁻¹ • y) = y
    module

/-- The finite stereographic parametrization is smooth as a map into the sphere. -/
@[category API, AMS 53]
private theorem counterexampleSphereChart_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ counterexampleSphereChart := by
  apply ContMDiff.codRestrict_sphere
  · have heq : (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) =
        fun z : ℂ ↦ (‖z‖ ^ 2 + 1)⁻¹ •
          (2 • (counterexampleTwoTangentEquiv z : ℝ³) +
            (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : ℝ³)) := by
      funext z
      exact counterexampleSphereChart_coe z
    exact (show ContDiff ℝ ∞ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) by
      rw [heq]
      have hs : ContDiff ℝ ∞ (fun z : ℂ ↦ ‖z‖ ^ 2) := contDiff_norm_sq ℝ
      have hT : ContDiff ℝ ∞
          (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³)) :=
        ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.contDiff.comp
          counterexampleTwoTangentEquiv.contDiff)
      have hone : ContDiff ℝ ∞ (fun _ : ℂ ↦ (1 : ℝ)) := contDiff_const
      have hnorth : ContDiff ℝ ∞ (fun _ : ℂ ↦ (counterexampleNorthPole : ℝ³)) :=
        contDiff_const
      exact ((hs.add contDiff_const).inv (fun z ↦ by positivity)).smul
        ((hT.const_smul 2).add ((hs.sub hone).smul hnorth))).contMDiff

/-- The reciprocal complex chart on the sphere. Its origin is the north pole and, away from
the origin, its finite coordinate is `100 / star w`. -/
private noncomputable def counterexampleTwoReciprocalSphereChart
    (w : ℂ) : sphere (0 : ℝ³) 1 :=
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : ℝ³)))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : ℝ³), by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent := Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  (stereographic' 2 (-counterexampleNorthPole)).symm (Uneg u)

/-- The old north-pole chart coordinate of the reciprocal spherical chart is its defining
complex coordinate. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalLinearCoord_reciprocalSphereChart (w : ℂ) :
    counterexampleTwoReciprocalLinearCoord
      ((stereographic' 2 (-counterexampleNorthPole))
        (counterexampleTwoReciprocalSphereChart w)) = w := by
  let Upos := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : ℝ³)))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : ℝ³), by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent := Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  have hu : (u : ℝ³) ∈ (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hu' := Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.2
    change inner ℝ (u : ℝ³) (-(counterexampleNorthPole : ℝ³)) = 0 at hu'
    simpa only [inner_neg_right, neg_eq_zero] using hu'
  rw [counterexampleTwoReciprocalSphereChart]
  change counterexampleTwoReciprocalLinearCoord
    ((stereographic' 2 (-counterexampleNorthPole))
      ((stereographic' 2 (-counterexampleNorthPole)).symm (Uneg u))) = w
  rw [(stereographic' 2 (-counterexampleNorthPole)).right_inv (by simp)]
  rw [counterexampleTwoReciprocalLinearCoord]
  simp only [u, Uneg, LinearIsometryEquiv.symm_apply_apply]
  change 50 • Complex.orthonormalBasisOneI.repr.symm
    (Upos ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection (u : ℝ³))) = w
  rw [show (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection (u : ℝ³) =
      ⟨u, hu⟩ by
    simpa using (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ
      |>.orthogonalProjection_mem_subspace_eq_self
        (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ)]
  have hu_eq : (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ) =
      (50 : ℝ)⁻¹ • counterexampleTwoTangentEquiv w := by
    apply Subtype.ext
    rfl
  rw [hu_eq, map_smul]
  simp only [counterexampleTwoTangentEquiv, Upos, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [map_smul, LinearIsometryEquiv.symm_apply_apply]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

/-- The reciprocal coordinate used at the north pole is smooth. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalLinearCoord_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocalLinearCoord := by
  let Upos := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
    (50 • Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Upos.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection.comp
          ((ℝ ∙ (-(counterexampleNorthPole : ℝ³)))ᗮ.subtypeL.comp
            Uneg.symm.toContinuousLinearEquiv.toContinuousLinearMap)))
  change ContDiff ℝ ∞ L
  exact L.contDiff

/-- The reciprocal linear coordinate is a similarity of ratio `50`. -/
@[category API, AMS 53]
private theorem norm_counterexampleTwoReciprocalLinearCoord
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖counterexampleTwoReciprocalLinearCoord x‖ = 50 * ‖x‖ := by
  let Upos := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u := Uneg.symm x
  have hu : (u : ℝ³) ∈ (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hu' := Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.2
    change inner ℝ (u : ℝ³) (-(counterexampleNorthPole : ℝ³)) = 0 at hu'
    simpa only [inner_neg_right, neg_eq_zero] using hu'
  rw [counterexampleTwoReciprocalLinearCoord]
  change ‖50 • Complex.orthonormalBasisOneI.repr.symm
    (Upos ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection (u : ℝ³)))‖ = _
  rw [show (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection (u : ℝ³) =
      ⟨u, hu⟩ by
    simpa using (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ
      |>.orthogonalProjection_mem_subspace_eq_self
        (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ),
    RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  change (50 : ℝ) * ‖(u : ℝ³)‖ = 50 * ‖x‖
  rw [Submodule.norm_coe, Uneg.symm.norm_map]

/-- The reciprocal linear coordinate is injective. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalLinearCoord_injective :
    Function.Injective counterexampleTwoReciprocalLinearCoord := by
  intro x y hxy
  have hsub : counterexampleTwoReciprocalLinearCoord (x - y) =
      counterexampleTwoReciprocalLinearCoord x - counterexampleTwoReciprocalLinearCoord y := by
    simp only [counterexampleTwoReciprocalLinearCoord, map_sub, Submodule.coe_sub, smul_sub]
  have hnorm := norm_counterexampleTwoReciprocalLinearCoord (x - y)
  rw [hsub, hxy, sub_self, norm_zero] at hnorm
  have : x - y = 0 := by
    rw [← norm_eq_zero]
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp this

/-- Every point except the south pole occurs in the reciprocal chart. -/
@[category API, AMS 53]
private theorem exists_reciprocalSphereChart_of_ne_south
    {p : sphere (0 : ℝ³) 1} (hp : p ≠ counterexampleSphereChart 0) :
    ∃ w : ℂ, counterexampleTwoReciprocalSphereChart w = p := by
  let e := stereographic' 2 (-counterexampleNorthPole)
  have hpole : p ∈ e.source := by
    dsimp only [e]
    rw [stereographic'_source]
    simpa [counterexampleSphereChart_zero] using hp
  let x := e p
  let w := counterexampleTwoReciprocalLinearCoord x
  have hrho : counterexampleTwoReciprocalSphereChart w ∈ e.source := by
    rw [counterexampleTwoReciprocalSphereChart]
    exact e.map_target (by simp [e])
  refine ⟨w, e.injOn hrho hpole ?_⟩
  apply counterexampleTwoReciprocalLinearCoord_injective
  rw [counterexampleTwoReciprocalLinearCoord_reciprocalSphereChart]

/-- In the chart centered at the north pole, the reciprocal of the original finite coordinate is
the fixed real-linear coordinate used by the smooth reciprocal representative. -/
@[category API, AMS 53]
private theorem counterexampleSphereCoord_oppositeChart_reciprocal
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    100 / star (counterexampleSphereCoord
        ((stereographic' 2 (-counterexampleNorthPole)).symm x)) =
          counterexampleTwoReciprocalLinearCoord x ∧
      counterexampleTwoReciprocalLinearCoord x ≠ 0 := by
  let Upos := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u := Uneg.symm x
  have hu : (u : ℝ³) ∈ (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hu_neg := Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.2
    change inner ℝ (u : ℝ³) (-(counterexampleNorthPole : ℝ³)) = 0 at hu_neg
    simpa only [inner_neg_right, neg_eq_zero] using hu_neg
  have hu0 : (u : ℝ³) ≠ 0 := by
    intro h
    have hu_zero : u = 0 := Subtype.ext h
    apply hx
    rw [← Uneg.apply_symm_apply x]
    simpa only [u, map_zero] using congrArg Uneg hu_zero
  have htransition := SphereSupport.stereoToFun_stereoInvFunAux_neg
    (norm_eq_of_mem_sphere counterexampleNorthPole) hu hu0
  have hchart :
      (stereographic' 2 counterexampleNorthPole)
          ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
        (4 / ‖x‖ ^ 2) • Upos (⟨u, hu⟩ :
          (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ) := by
    change Upos (stereoToFun (counterexampleNorthPole : ℝ³)
      (stereoInvFunAux (-(counterexampleNorthPole : ℝ³)) (u : ℝ³))) = _
    have hunorm : ‖(u : ℝ³)‖ = ‖x‖ := by
      rw [Submodule.norm_coe, Uneg.symm.norm_map]
    rw [htransition, map_smul, hunorm]
  let y : ℂ := Complex.orthonormalBasisOneI.repr.symm
    (Upos (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ))
  have hcoord : counterexampleSphereCoord
      ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
        (2 / ‖x‖ ^ 2) • y := by
    rw [counterexampleSphereCoord, hchart]
    simp only [map_smul, smul_smul]
    apply congrArg (fun c : ℝ ↦ c • y)
    field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]
    ring
  have hnormy : ‖y‖ = ‖x‖ := by
    simp only [y, LinearIsometryEquiv.norm_map]
    change ‖(u : ℝ³)‖ = ‖x‖
    rw [Submodule.norm_coe, Uneg.symm.norm_map]
  have hy0 : y ≠ 0 := by
    rw [← norm_ne_zero_iff, hnormy]
    exact norm_ne_zero_iff.mpr hx
  have hsquare : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hstar : star y * y = (‖x‖ ^ 2 : ℂ) := by
    rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hnormy]
    norm_num
  have hlinear : counterexampleTwoReciprocalLinearCoord x = 50 • y := by
    rw [counterexampleTwoReciprocalLinearCoord]
    change 50 • Complex.orthonormalBasisOneI.repr.symm
      (Upos ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection (u : ℝ³))) =
        50 • y
    rw [show (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.orthogonalProjection (u : ℝ³) =
        ⟨u, hu⟩ by
      simpa using (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ
        |>.orthogonalProjection_mem_subspace_eq_self
          (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ)]
  constructor
  · rw [hcoord, hlinear]
    have hdenom : star ((2 / ‖x‖ ^ 2) • y) ≠ 0 := by
      rw [star_smul]
      exact smul_ne_zero (div_ne_zero (by norm_num) hsquare) (star_ne_zero.mpr hy0)
    rw [div_eq_iff hdenom]
    rw [star_smul]
    simp only [star_trivial]
    simp only [nsmul_eq_mul, Complex.real_smul]
    change (100 : ℂ) = 50 * y * (((2 / ‖x‖ ^ 2 : ℝ) : ℂ) * star y)
    rw [show 50 * y * (((2 / ‖x‖ ^ 2 : ℝ) : ℂ) * star y) =
      50 * ((2 / ‖x‖ ^ 2 : ℝ) : ℂ) * (star y * y) by ring, hstar]
    push_cast
    field_simp [norm_ne_zero_iff.mpr hx] ; norm_num
  · rw [hlinear]
    exact smul_ne_zero (by norm_num) hy0

/-- The inverse stereographic chart based at the south pole sends its origin to the north pole. -/
@[category API, AMS 53]
private theorem counterexampleOppositeSphereChart_zero :
    (stereographic' 2 (-counterexampleNorthPole)).symm 0 = counterexampleNorthPole := by
  apply Subtype.ext
  simp [stereographic'_symm_apply]

/-- In the north-pole chart, the pointwise extension is exactly the smooth reciprocal
representative composed with a fixed real-linear coordinate. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_oppositeChart
    (x : EuclideanSpace ℝ (Fin 2)) :
    counterexampleTwoSphereExtension
        ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
      counterexampleTwoReciprocal (counterexampleTwoReciprocalLinearCoord x) := by
  by_cases hx : x = 0
  · subst x
    have hlinear : counterexampleTwoReciprocalLinearCoord 0 = 0 := by
      simp [counterexampleTwoReciprocalLinearCoord]
    rw [counterexampleOppositeSphereChart_zero, hlinear, counterexampleTwoReciprocal_zero]
    simp [counterexampleTwoSphereExtension]
  · have htransition := counterexampleSphereCoord_oppositeChart_reciprocal hx
    have hpole :
        (stereographic' 2 (-counterexampleNorthPole)).symm x ≠
          counterexampleNorthPole := by
      intro h
      have hzero := counterexampleOppositeSphereChart_zero
      exact hx ((stereographic' 2 (-counterexampleNorthPole)).symm.injOn
        (by simp) (by simp) (h.trans hzero.symm))
    have hcoord : counterexampleSphereCoord
        ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
          100 / star (counterexampleTwoReciprocalLinearCoord x) := by
      calc
        counterexampleSphereCoord
            ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
            100 / star (100 / star (counterexampleSphereCoord
              ((stereographic' 2 (-counterexampleNorthPole)).symm x))) :=
          (hundred_div_star_involutive _).symm
        _ = 100 / star (counterexampleTwoReciprocalLinearCoord x) := by
          rw [htransition.1]
    rw [counterexampleTwoSphereExtension, if_neg hpole, hcoord]
    exact counterexample_two_reciprocal htransition.2

/-- The reciprocal chart pulls the spherical extension back to the explicit reciprocal
representative. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_reciprocalSphereChart (w : ℂ) :
    counterexampleTwoSphereExtension (counterexampleTwoReciprocalSphereChart w) =
      counterexampleTwoReciprocal w := by
  let e := stereographic' 2 (-counterexampleNorthPole)
  have hrho : counterexampleTwoReciprocalSphereChart w ∈ e.source := by
    rw [counterexampleTwoReciprocalSphereChart]
    exact e.map_target (by simp [e])
  calc
    counterexampleTwoSphereExtension (counterexampleTwoReciprocalSphereChart w) =
        counterexampleTwoSphereExtension
          (e.symm (e (counterexampleTwoReciprocalSphereChart w))) := by
      rw [e.left_inv hrho]
    _ = counterexampleTwoReciprocal
        (counterexampleTwoReciprocalLinearCoord
          (e (counterexampleTwoReciprocalSphereChart w))) := by
      exact counterexampleTwoSphereExtension_oppositeChart _
    _ = counterexampleTwoReciprocal w := by
      rw [counterexampleTwoReciprocalLinearCoord_reciprocalSphereChart]

/-- Ambient rational formula for the reciprocal spherical chart. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalSphereChart_coe (w : ℂ) :
    (counterexampleTwoReciprocalSphereChart w : ℝ³) =
      (‖w‖ ^ 2 + 10000)⁻¹ •
        (200 • (counterexampleTwoTangentEquiv w : ℝ³) +
          (10000 - ‖w‖ ^ 2) • (counterexampleNorthPole : ℝ³)) := by
  let Uneg := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := ℝ³) 2
    (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : ℝ³)))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : ℝ³), by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent := Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  rw [counterexampleTwoReciprocalSphereChart, stereographic'_symm_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  change (‖(u : ℝ³)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (u : ℝ³) +
      (‖(u : ℝ³)‖ ^ 2 + 4)⁻¹ • (‖(u : ℝ³)‖ ^ 2 - 4) •
        (-(counterexampleNorthPole : ℝ³)) = _
  have hunorm : ‖(u : ℝ³)‖ ^ 2 = ‖w‖ ^ 2 / 2500 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by norm_num :
      (0 : ℝ) < 50), Submodule.norm_coe,
      counterexampleTwoTangentEquiv.norm_map]
    ring
  rw [hunorm]
  simp only [u, ← Nat.cast_smul_eq_nsmul ℝ 200, smul_smul,
    smul_neg, smul_add]
  have htangent : (‖w‖ ^ 2 / 2500 + 4)⁻¹ * (4 * 50⁻¹) =
      (‖w‖ ^ 2 + 10000)⁻¹ * 200 := by
    field_simp
    ring
  have hpole : -((‖w‖ ^ 2 / 2500 + 4)⁻¹ * (‖w‖ ^ 2 / 2500 - 4)) =
      (‖w‖ ^ 2 + 10000)⁻¹ * (10000 - ‖w‖ ^ 2) := by
    field_simp
    ring
  rw [← neg_smul, htangent, hpole]
  norm_num [← Nat.cast_smul_eq_nsmul ℝ 200, smul_smul]

/-- Derivative of the rational reciprocal chart in ambient coordinates. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalSphereChart_fderiv_apply (w v : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w v =
      (200 / (‖w‖ ^ 2 + 10000)) • (counterexampleTwoTangentEquiv v : ℝ³) -
        (400 * inner ℝ w v / (‖w‖ ^ 2 + 10000) ^ 2) •
          (counterexampleTwoTangentEquiv w : ℝ³) -
        (40000 * inner ℝ w v / (‖w‖ ^ 2 + 10000) ^ 2) •
          (counterexampleNorthPole : ℝ³) := by
  let T : ℂ →L[ℝ] ℝ³ :=
    (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hT : HasFDerivAt (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³)) T w :=
    T.hasFDerivAt
  have hs : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2) ((2 : ℝ) • innerSL ℝ w) w := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hden : HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 + 10000)⁻¹)
      (-((‖w‖ ^ 2 + 10000) ^ 2)⁻¹ • ((2 : ℝ) • innerSL ℝ w)) w := by
    convert (hasDerivAt_inv (by positivity : ‖w‖ ^ 2 + 10000 ≠ 0)).hasFDerivAt.comp w
      (hs.add_const 10000) using 1
    all_goals
      ext x
      simp
      ring
  have hnum : HasFDerivAt
      (fun z : ℂ ↦ (200 : ℝ) • (counterexampleTwoTangentEquiv z : ℝ³) +
        (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : ℝ³))
      ((200 : ℝ) • T + (-((2 : ℝ) • innerSL ℝ w)).smulRight
        (counterexampleNorthPole : ℝ³)) w := by
    convert (hT.const_smul 200).add
      ((hasFDerivAt_const (x := w) 10000).sub hs |>.smul_const
        (counterexampleNorthPole : ℝ³)) using 1
    all_goals
      ext x
      simp
  have hderiv := hden.smul hnum
  have heq : (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) =
      fun z : ℂ ↦ (‖z‖ ^ 2 + 10000)⁻¹ •
        ((200 : ℝ) • (counterexampleTwoTangentEquiv z : ℝ³) +
          (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : ℝ³)) := by
    funext z
    simpa only [← Nat.cast_smul_eq_nsmul ℝ 200] using
      counterexampleTwoReciprocalSphereChart_coe z
  rw [heq]
  change (fderiv ℝ
    (((fun z : ℂ ↦ (‖z‖ ^ 2 + 10000)⁻¹) •
      fun z ↦ (200 : ℝ) • (counterexampleTwoTangentEquiv z : ℝ³) +
        (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : ℝ³))) w) v = _
  rw [hderiv.fderiv]
  dsimp only [T]
  have hTv : (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL
      (counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap v) =
        (counterexampleTwoTangentEquiv v : ℝ³) := rfl
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, innerSL_apply_apply,
    smul_add, smul_smul, neg_smul]
  rw [hTv]
  change _ = _
  match_scalars <;> (try simp only [smul_eq_mul]) <;>
    field_simp [show ‖w‖ ^ 2 + 10000 ≠ 0 by positivity] <;> ring

/-- The reciprocal spherical chart is conformal, with scale `200 / (‖w‖² + 10000)`.
Both the inner-product and norm forms are recorded because the radius estimates use each. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalSphereChart_conformal (w v t : ℂ) :
    inner ℝ
        (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w v)
        (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w t) =
        40000 / (‖w‖ ^ 2 + 10000) ^ 2 * inner ℝ v t ∧
      ‖fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w v‖ =
        200 / (‖w‖ ^ 2 + 10000) * ‖v‖ := by
  have hT (a b : ℂ) : inner ℝ (counterexampleTwoTangentEquiv a : ℝ³)
      (counterexampleTwoTangentEquiv b : ℝ³) = inner ℝ a b :=
    counterexampleTwoTangentEquiv.inner_map_map a b
  have hTn (a : ℂ) : inner ℝ (counterexampleTwoTangentEquiv a : ℝ³)
      (counterexampleNorthPole : ℝ³) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp
      (counterexampleTwoTangentEquiv a).2
  have hnT (a : ℂ) : inner ℝ (counterexampleNorthPole : ℝ³)
      (counterexampleTwoTangentEquiv a : ℝ³) = 0 := by
    rw [real_inner_comm, hTn]
  have hnn : inner ℝ (counterexampleNorthPole : ℝ³)
      (counterexampleNorthPole : ℝ³) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere counterexampleNorthPole]
    norm_num
  have hinner (a b : ℂ) : inner ℝ
        (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w a)
        (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w b) =
      40000 / (‖w‖ ^ 2 + 10000) ^ 2 * inner ℝ a b := by
    rw [counterexampleTwoReciprocalSphereChart_fderiv_apply,
      counterexampleTwoReciprocalSphereChart_fderiv_apply]
    simp only [inner_sub_left, inner_sub_right,
      real_inner_smul_left,
      real_inner_smul_right, hT, hTn, hnT, hnn, mul_zero, sub_zero]
    rw [real_inner_comm a w, real_inner_comm b w]
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring
  refine ⟨hinner v t, ?_⟩
  have hsquare := hinner v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsquare
  have hden : 0 < ‖w‖ ^ 2 + 10000 := by positivity
  have hscale : 0 ≤ 200 / (‖w‖ ^ 2 + 10000) := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hscale (norm_nonneg _))).mp
  calc
    ‖fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w v‖ ^ 2 =
        40000 / (‖w‖ ^ 2 + 10000) ^ 2 * ‖v‖ ^ 2 := hsquare
    _ = (200 / (‖w‖ ^ 2 + 10000) * ‖v‖) ^ 2 := by
      field_simp
      ring

/-- The ambient differential of the reciprocal chart has exactly the tangent plane as its
range. -/
@[category API, AMS 53]
private theorem range_fderiv_counterexampleTwoReciprocalSphereChart (w : ℂ) :
    (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w).range =
      (ℝ ∙ (counterexampleTwoReciprocalSphereChart w : ℝ³))ᗮ := by
  let dρ : ℂ →L[ℝ] ℝ³ :=
    fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w
  have hdρinj : Function.Injective dρ := by
    intro v t hvt
    have hscale := (counterexampleTwoReciprocalSphereChart_conformal w (v - t) (v - t)).2
    change ‖dρ (v - t)‖ = 200 / (‖w‖ ^ 2 + 10000) * ‖v - t‖ at hscale
    rw [map_sub, hvt, sub_self, norm_zero] at hscale
    have hpositive : 0 < 200 / (‖w‖ ^ 2 + 10000) := by positivity
    have : ‖v - t‖ = 0 := by nlinarith [norm_nonneg (v - t)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hdρorth (v : ℂ) : inner ℝ (dρ v)
      (counterexampleTwoReciprocalSphereChart w : ℝ³) = 0 := by
    have hT (a b : ℂ) : inner ℝ (counterexampleTwoTangentEquiv a : ℝ³)
        (counterexampleTwoTangentEquiv b : ℝ³) = inner ℝ a b :=
      counterexampleTwoTangentEquiv.inner_map_map a b
    have hTn (a : ℂ) : inner ℝ (counterexampleTwoTangentEquiv a : ℝ³)
        (counterexampleNorthPole : ℝ³) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (counterexampleTwoTangentEquiv a).2
    have hnT (a : ℂ) : inner ℝ (counterexampleNorthPole : ℝ³)
        (counterexampleTwoTangentEquiv a : ℝ³) = 0 := by
      rw [real_inner_comm, hTn]
    have hnn : inner ℝ (counterexampleNorthPole : ℝ³)
        (counterexampleNorthPole : ℝ³) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere counterexampleNorthPole]
      norm_num
    change inner ℝ
      (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w v)
      (counterexampleTwoReciprocalSphereChart w : ℝ³) = 0
    rw [counterexampleTwoReciprocalSphereChart_fderiv_apply,
      counterexampleTwoReciprocalSphereChart_coe]
    simp only [← Nat.cast_smul_eq_nsmul ℝ 200, inner_sub_left, real_inner_smul_left,
      real_inner_smul_right,
      inner_add_right, hT, hTn, hnT, hnn, mul_zero]
    rw [real_inner_comm v w, real_inner_self_eq_norm_sq]
    field_simp
    ring
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hdρorth v)
  · have hker : dρ.ker = ⊥ := LinearMap.ker_eq_bot.mpr hdρinj
    have hrank := LinearMap.finrank_range_add_finrank_ker dρ.toLinearMap
    rw [hker, finrank_bot, add_zero, Complex.finrank_real_complex] at hrank
    rw [hrank, Submodule.finrank_orthogonal_span_singleton (n := 2)
      (ne_zero_of_mem_unit_sphere (counterexampleTwoReciprocalSphereChart w))]

/-- The reciprocal chart is smooth as a map into the sphere. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalSphereChart_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ counterexampleTwoReciprocalSphereChart := by
  apply ContMDiff.codRestrict_sphere
  · have heq : (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) =
        fun z : ℂ ↦ (‖z‖ ^ 2 + 10000)⁻¹ •
          (200 • (counterexampleTwoTangentEquiv z : ℝ³) +
            (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : ℝ³)) := by
      funext z
      exact counterexampleTwoReciprocalSphereChart_coe z
    exact (show ContDiff ℝ ∞
        (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) by
      rw [heq]
      have hs : ContDiff ℝ ∞ (fun z : ℂ ↦ ‖z‖ ^ 2) := contDiff_norm_sq ℝ
      have hT : ContDiff ℝ ∞
          (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³)) :=
        ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.contDiff.comp
          counterexampleTwoTangentEquiv.contDiff)
      have htenThousand : ContDiff ℝ ∞ (fun _ : ℂ ↦ (10000 : ℝ)) := contDiff_const
      have hnorth : ContDiff ℝ ∞ (fun _ : ℂ ↦ (counterexampleNorthPole : ℝ³)) :=
        contDiff_const
      exact ((hs.add contDiff_const).inv (fun z ↦ by positivity)).smul
        ((hT.const_smul 200).add
          ((htenThousand.sub hs).smul hnorth))).contMDiff

/-- The pointwise extension is smooth at the north pole in the opposite stereographic chart. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_contMDiffAt_north :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension
      counterexampleNorthPole := by
  let e := stereographic' 2 (-counterexampleNorthPole)
  have he : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ (sphere (0 : ℝ³) 1) :=
    IsManifold.subset_maximalAtlas ⟨-counterexampleNorthPole, rfl⟩
  have hnorth : counterexampleNorthPole ∈ e.source := by
    simpa [e, stereographic'_source] using
      ne_neg_of_mem_unit_sphere ℝ counterexampleNorthPole
  have he_smooth : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ e
      counterexampleNorthPole :=
    contMDiffAt_of_mem_maximalAtlas he hnorth
  have hrepresentative : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ counterexampleTwoReciprocal (counterexampleTwoReciprocalLinearCoord x)) :=
    (counterexampleTwoReciprocal_contDiff.comp
      counterexampleTwoReciprocalLinearCoord_contDiff).contMDiff
  have hcomp : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p ↦ counterexampleTwoReciprocal (counterexampleTwoReciprocalLinearCoord (e p)))
      counterexampleNorthPole :=
    hrepresentative.contMDiffAt.comp counterexampleNorthPole he_smooth
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hnorth] with p hp
  simpa [e, e.left_inv hp] using
    counterexampleTwoSphereExtension_oppositeChart (e p)

/-- The planar expression `counterexample 2` extends smoothly through the missing north pole of
the stereographic chart. -/
@[category research solved, AMS 26 53]
theorem counterexample_two_sphere_extension :
    ∃ h : sphere (0 : ℝ³) 1 → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      ∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z := by
  exact ⟨counterexampleTwoSphereExtension,
    counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
      counterexampleTwoSphereExtension_contMDiffAt_north,
    counterexampleTwoSphereExtension_chart⟩

/-- The smooth spherical extension is uniquely determined by its values in the finite
stereographic chart. -/
@[category API, AMS 53]
private theorem eq_counterexampleTwoSphereExtension
    (h : sphere (0 : ℝ³) 1 → ℝ)
    (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hchart : ∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) :
    h = counterexampleTwoSphereExtension := by
  funext p
  by_cases hp : p = counterexampleNorthPole
  · subst p
    let e := stereographic' 2 (-counterexampleNorthPole)
    have hecont : Continuous e.symm := by
      rw [← continuousOn_univ]
      simpa [e] using e.symm.continuousOn
    have heq : (fun x : EuclideanSpace ℝ (Fin 2) ↦ h (e.symm x)) =
        fun x ↦ counterexampleTwoSphereExtension (e.symm x) := by
      apply Continuous.ext_on (dense_compl_singleton (0 : EuclideanSpace ℝ (Fin 2)))
        (hsmooth.continuous.comp hecont)
        ((counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
          counterexampleTwoSphereExtension_contMDiffAt_north).continuous.comp hecont)
      intro x hx
      have hx0 : x ≠ 0 := by simpa using hx
      have hpole : e.symm x ≠ counterexampleNorthPole := by
        intro h
        have hzero : e.symm 0 = counterexampleNorthPole := by
          simpa [e] using counterexampleOppositeSphereChart_zero
        exact hx0 (e.symm.injOn (by simp [e]) (by simp [e]) (h.trans hzero.symm))
      change h (e.symm x) = counterexampleTwoSphereExtension (e.symm x)
      rw [← counterexampleSphereChart_coord hpole, hchart,
        counterexampleTwoSphereExtension_chart]
    simpa [e, counterexampleOppositeSphereChart_zero] using congrFun heq 0
  · rw [← counterexampleSphereChart_coord hp, hchart,
      counterexampleTwoSphereExtension_chart]

/-- The constant term dominates the oscillatory term by a vast margin. -/
@[category API, AMS 53]
private theorem counterexample_two_lower (z : ℂ) :
    (1 : ℝ) ≤ counterexample 2 z := by
  let r := ‖z‖
  let w := (100 / star z) ^ ((2 : ℂ) / 2)
  let c := r ^ 2 * Real.exp (-r ^ (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) /
    (1 + r ^ 2)
  have hr : 0 ≤ r := norm_nonneg z
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hexp : Real.exp (-r ^ (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hr _))
      (Real.exp_nonneg _)
  have hratio : r ^ 2 / (1 + r ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 1 + r ^ 2)]
    linarith [sq_nonneg r]
  have hc1 : c ≤ 1 := by
    calc
      c = (r ^ 2 / (1 + r ^ 2)) *
          Real.exp (-r ^ (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) := by
        dsimp [c]
        ring
      _ ≤ 1 * 1 := mul_le_mul hratio hexp (Real.exp_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hseed : -(253 / 160 : ℝ) ≤ counterexampleSeed w :=
    neg_le_of_abs_le (counterexampleSeed_abs_le w)
  have hproduct : -(253 / 160 : ℝ) ≤ c * counterexampleSeed w := by
    calc
      -(253 / 160 : ℝ) ≤ c * (-(253 / 160 : ℝ)) := by nlinarith
      _ ≤ c * counterexampleSeed w := mul_le_mul_of_nonneg_left hseed hc0
  have hproduct' : -(253 / 160 : ℝ) ≤
      ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-(‖z‖ ^ 2))) *
        counterexampleSeed ((100 / star z) ^ ((2 : ℂ) / 2)) / (1 + ‖z‖ ^ 2) := by
    calc
      -(253 / 160 : ℝ) ≤ c * counterexampleSeed w := hproduct
      _ = _ := by
        dsimp [c, r, w]
        ring
  rw [counterexample]
  norm_num at hproduct' ⊢
  linarith

/-- The explicit spherical extension is uniformly positive, so its support body contains a
unit ball. -/
@[category API, AMS 53]
private theorem counterexampleTwoSphereExtension_lower
    (p : sphere (0 : ℝ³) 1) : (1 : ℝ) ≤ counterexampleTwoSphereExtension p := by
  by_cases hp : p = counterexampleNorthPole
  · simp [counterexampleTwoSphereExtension, hp]
    norm_num
  · rw [counterexampleTwoSphereExtension, if_neg hp]
    exact counterexample_two_lower _

/-- The homogeneous extension is nonnegative in every ambient direction. -/
@[category API, AMS 53]
private theorem counterexampleTwoRadialExtension_nonneg (x : ℝ³) :
    0 ≤ SphereSupport.radialExtension counterexampleTwoSphereExtension x := by
  by_cases hx : x = 0
  · simp [hx, SphereSupport.radialExtension]
  · rw [SphereSupport.radialExtension, dif_neg hx]
    exact mul_nonneg (norm_nonneg x)
      (le_trans zero_le_one (counterexampleTwoSphereExtension_lower _))

/-- A coarse uniform bound for the power-times-exponential terms in the reciprocal-chart
estimates. The extra `1` lets the proof split at `y = 1` without optimizing a maximum. -/
@[category API, AMS 53]
private theorem rpow_mul_exp_neg_le_factorial {y c a : ℝ} (n : ℕ)
    (hy : 0 ≤ y) (hc : 0 < c) (ha : 0 ≤ a) (han : a ≤ n) :
    y ^ a * Real.exp (-c * y) ≤ 1 + n.factorial / c ^ n := by
  by_cases hy1 : y ≤ 1
  · calc
      y ^ a * Real.exp (-c * y) ≤ 1 * 1 := by
        exact mul_le_mul (Real.rpow_le_one hy hy1 ha)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hy))
          (Real.exp_nonneg _) zero_le_one
      _ ≤ 1 + n.factorial / c ^ n := by
        simpa only [one_mul] using
          (le_add_of_nonneg_right (show 0 ≤ n.factorial / c ^ n by positivity))
  · have h1y : 1 ≤ y := le_of_not_ge hy1
    have hpower : y ^ a ≤ y ^ n := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le h1y han
    have hfactorial : (0 : ℝ) < n.factorial := by positivity
    have hexp := Real.pow_div_factorial_le_exp (x := c * y) (mul_nonneg hc.le hy) n
    have hpowexp : c ^ n * y ^ n ≤ n.factorial * Real.exp (c * y) := by
      have := (div_le_iff₀ hfactorial).mp hexp
      simpa only [mul_pow, mul_comm] using this
    have hquotient : y ^ n / Real.exp (c * y) ≤ n.factorial / c ^ n := by
      rw [div_le_div_iff₀ (Real.exp_pos _) (pow_pos hc n)]
      simpa only [mul_comm] using hpowexp
    calc
      y ^ a * Real.exp (-c * y) ≤ y ^ n * Real.exp (-c * y) :=
        mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _)
      _ = y ^ n / Real.exp (c * y) := by
        rw [show -c * y = -(c * y) by ring, Real.exp_neg]
        rfl
      _ ≤ n.factorial / c ^ n := hquotient
      _ ≤ 1 + n.factorial / c ^ n := le_add_of_nonneg_left zero_le_one

/-- The elementary exact maximum estimate for `t ^ a * exp (-t)`. It avoids introducing a
calculus maximizer into each reciprocal-chart coefficient bound. -/
@[category API, AMS 53]
private theorem rpow_mul_exp_neg_le_self {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) :
    t ^ a * Real.exp (-t) ≤ a ^ a * Real.exp (-a) := by
  obtain rfl | ht := ht.eq_or_lt
  · simp [Real.zero_rpow ha.ne']
    positivity
  · have hlog := Real.log_le_sub_one_of_pos (div_pos ht ha)
    have hlog' : a * Real.log t - t ≤ a * Real.log a - a := by
      have h := mul_le_mul_of_nonneg_left hlog ha.le
      rw [Real.log_div ht.ne' ha.ne'] at h
      field_simp [ha.ne'] at h
      linarith
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ha, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)

/-- For the exponents used below, the exact maximum admits a very simple rational upper bound. -/
@[category API, AMS 53]
private theorem self_rpow_mul_exp_neg_le_half {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    a ^ a * Real.exp (-a) ≤ a / 2 := by
  have ha : 0 ≤ a := zero_le_one.trans ha1
  have hquot0 : 0 ≤ a / Real.exp 1 := div_nonneg ha (Real.exp_nonneg _)
  have hquot1 : a / Real.exp 1 ≤ 1 := by
    rw [div_le_one (Real.exp_pos _)]
    exact ha2.trans Real.exp_one_gt_two.le
  calc
    a ^ a * Real.exp (-a) = (a / Real.exp 1) ^ a := by
      rw [show -a = (-1) * a by ring, Real.exp_mul, Real.exp_neg,
        ← Real.mul_rpow ha (inv_nonneg.mpr (Real.exp_nonneg 1)), div_eq_mul_inv]
    _ ≤ a / Real.exp 1 := Real.rpow_le_self_of_le_one hquot0 hquot1 ha1
    _ ≤ a / 2 := div_le_div_of_nonneg_left ha (by norm_num) Real.exp_one_gt_two.le

/-- For exponents at most one, the unscaled power-times-exponential maximum is at most one. -/
@[category API, AMS 53]
private theorem rpow_mul_exp_neg_le_one {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (ha1 : a ≤ 1) :
    t ^ a * Real.exp (-t) ≤ 1 := by
  refine (rpow_mul_exp_neg_le_self ht ha).trans ?_
  calc
    a ^ a * Real.exp (-a) ≤ 1 * 1 := by
      exact mul_le_mul (Real.rpow_le_one ha.le ha1 ha.le)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha.le)) (Real.exp_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- With exponent at most four, doubling the exponential rate makes the same maximum at most
one. This single loose estimate controls the largest term in the second damping derivative. -/
@[category API, AMS 53]
private theorem rpow_mul_exp_neg_two_mul_le_one {t a : ℝ}
    (ht : 0 ≤ t) (ha : 0 < a) (ha4 : a ≤ 4) :
    t ^ a * Real.exp (-2 * t) ≤ 1 := by
  have hmax := rpow_mul_exp_neg_le_self (t := 2 * t) (a := a) (mul_nonneg (by norm_num) ht) ha
  have hself : a ^ a * Real.exp (-a) ≤ (2 : ℝ) ^ a := by
    rw [show -a = (-1) * a by ring, Real.exp_mul, Real.exp_neg,
      ← Real.mul_rpow ha.le (inv_nonneg.mpr (Real.exp_nonneg 1)), ← div_eq_mul_inv]
    exact Real.rpow_le_rpow (div_nonneg ha.le (Real.exp_nonneg _))
      (by rw [div_le_iff₀ (Real.exp_pos _)]; nlinarith [Real.exp_one_gt_two]) ha.le
  have hscaled : (2 : ℝ) ^ a * (t ^ a * Real.exp (-2 * t)) ≤ (2 : ℝ) ^ a := by
    calc
      (2 : ℝ) ^ a * (t ^ a * Real.exp (-2 * t)) =
          (2 * t) ^ a * Real.exp (-(2 * t)) := by
        rw [Real.mul_rpow (by norm_num) ht]
        ring
      _ ≤ a ^ a * Real.exp (-a) := hmax
      _ ≤ (2 : ℝ) ^ a := hself
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  exact le_of_mul_le_mul_left (by simpa using hscaled) hpos

/-- The first reciprocal damping-derivative numerator is at most one. -/
@[category API, AMS 53]
private theorem reciprocalDampingFirstNumerator_bound {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) * ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ)) ≤ 1 := by
  have hsmall : t ^ (3 / 8 : ℝ) * Real.exp (-t) ≤ 1 :=
    rpow_mul_exp_neg_le_one ht (by norm_num) (by norm_num)
  have hlarge : t ^ (11 / 8 : ℝ) * Real.exp (-t) ≤ 11 / 16 :=
    (rpow_mul_exp_neg_le_self ht (by norm_num)).trans
      ((self_rpow_mul_exp_neg_le_half (a := 11 / 8) (by norm_num) (by norm_num)).trans_eq
        (by norm_num))
  calc
    Real.exp (-t) * ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ)) =
        (1 / 8 : ℝ) * (t ^ (3 / 8 : ℝ) * Real.exp (-t)) +
          t ^ (11 / 8 : ℝ) * Real.exp (-t) := by ring
    _ ≤ (1 / 8 : ℝ) * 1 + 11 / 16 := by gcongr
    _ ≤ 1 := by norm_num

/-- The six terms in the second reciprocal damping-derivative numerator admit the rational
bound used in the global uniqueness and radius estimates. -/
@[category API, AMS 53]
private theorem reciprocalDampingSecondNumerator_bound {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-2 * t) * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
        (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) +
      Real.exp (-t) * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
        (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ)) < 10 := by
  have hexp_two_le (a : ℝ) :
      t ^ a * Real.exp (-2 * t) ≤ t ^ a * Real.exp (-t) := by
    gcongr
    nlinarith
  have h₁ : t ^ (3 / 4 : ℝ) * Real.exp (-2 * t) ≤ 1 :=
    rpow_mul_exp_neg_two_mul_le_one ht (by norm_num) (by norm_num)
  have h₂ : t ^ (7 / 4 : ℝ) * Real.exp (-2 * t) ≤ 7 / 8 :=
    (hexp_two_le (7 / 4)).trans <|
      (rpow_mul_exp_neg_le_self ht (by norm_num)).trans
        ((self_rpow_mul_exp_neg_le_half (a := 7 / 4) (by norm_num) (by norm_num)).trans_eq
          (by norm_num))
  have h₃ : t ^ (11 / 4 : ℝ) * Real.exp (-2 * t) ≤ 1 :=
    rpow_mul_exp_neg_two_mul_le_one ht (by norm_num) (by norm_num)
  have h₄ : t ^ (7 / 8 : ℝ) * Real.exp (-t) ≤ 1 :=
    rpow_mul_exp_neg_le_one ht (by norm_num) (by norm_num)
  have h₅ : t ^ (15 / 8 : ℝ) * Real.exp (-t) ≤ 15 / 16 :=
    (rpow_mul_exp_neg_le_self ht (by norm_num)).trans
      ((self_rpow_mul_exp_neg_le_half (a := 15 / 8) (by norm_num) (by norm_num)).trans_eq
        (by norm_num))
  have h₆ : t ^ (23 / 8 : ℝ) * Real.exp (-t) ≤ 7 := by
    convert rpow_mul_exp_neg_le_factorial 3 ht (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 23 / 8) (by norm_num : (23 / 8 : ℝ) ≤ 3) using 1 <;>
      norm_num [Nat.factorial]
  calc
    Real.exp (-2 * t) * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
        (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) +
      Real.exp (-t) * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
        (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ)) =
        (1 / 64 : ℝ) * (t ^ (3 / 4 : ℝ) * Real.exp (-2 * t)) +
        (1 / 4 : ℝ) * (t ^ (7 / 4 : ℝ) * Real.exp (-2 * t)) +
        t ^ (11 / 4 : ℝ) * Real.exp (-2 * t) +
        (7 / 64 : ℝ) * (t ^ (7 / 8 : ℝ) * Real.exp (-t)) +
        (7 / 4 : ℝ) * (t ^ (15 / 8 : ℝ) * Real.exp (-t)) +
        t ^ (23 / 8 : ℝ) * Real.exp (-t) := by ring
    _ ≤ (1 / 64 : ℝ) * 1 + (1 / 4 : ℝ) * (7 / 8) + 1 +
        (7 / 64 : ℝ) * 1 + (7 / 4 : ℝ) * (15 / 16) + 7 := by gcongr
    _ < 10 := by norm_num

/-- The reciprocal-chart conformal weight times the damping factor has a deliberately coarse
global numerical bound. This is the main growth estimate behind the radius-tensor certificate. -/
@[category API, AMS 53]
private theorem reciprocalMetricDamping_bound {y : ℝ} (hy : 0 ≤ y) :
    2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) <
      164000000 := by
  by_cases hy2 : y ≤ 2
  · have hy8 : y ^ 8 ≤ (2 : ℝ) ^ 8 := pow_le_pow_left₀ hy hy2 8
    have hpsi : 0 ≤ y * Real.exp (-(y ^ (-(8 : ℝ)))) :=
      mul_nonneg hy (Real.exp_nonneg _)
    calc
      2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) ≤
          2500 * (1 + (2 : ℝ) ^ 8) * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpsi)
      _ < 164000000 := by norm_num
  · have hy8 : (256 : ℝ) ≤ y ^ 8 := by
      convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (le_of_not_ge hy2) 8 using 1 ;
        norm_num
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num) (le_of_not_ge hy2)
    have hinv : y ^ (-(8 : ℝ)) ≤ 1 / 256 := by
      rw [Real.rpow_neg hy]
      have hy8r : y ^ (8 : ℝ) = y ^ (8 : ℕ) := Real.rpow_natCast y 8
      calc
        (y ^ (8 : ℝ))⁻¹ = (y ^ (8 : ℕ))⁻¹ := by rw [hy8r]
        _ ≤ (256 : ℝ)⁻¹ :=
          (inv_le_inv₀ (pow_pos hypos 8) (by norm_num)).2 hy8
        _ = 1 / 256 := by norm_num
    have hdamping : (255 / 256 : ℝ) ≤ Real.exp (-(y ^ (-(8 : ℝ)))) := by
      calc
        (255 / 256 : ℝ) = 1 - 1 / 256 := by norm_num
        _ ≤ 1 - y ^ (-(8 : ℝ)) := sub_le_sub_left hinv 1
        _ ≤ Real.exp (-(y ^ (-(8 : ℝ)))) := Real.one_sub_le_exp_neg _
    have hexp : Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) ≤
        Real.exp (-(255 / 256 : ℝ) * y) := by
      rw [Real.exp_le_exp]
      simpa [mul_comm] using neg_le_neg (mul_le_mul_of_nonneg_left hdamping hy)
    have hpower := rpow_mul_exp_neg_le_factorial 8 hy
      (by norm_num : (0 : ℝ) < 255 / 256) (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (8 : ℝ) ≤ 8)
    have hpower' : y ^ 8 * Real.exp (-(255 / 256 : ℝ) * y) ≤
        1 + (8 : ℕ).factorial / (255 / 256 : ℝ) ^ 8 := by
      convert hpower using 1 ; norm_num
    have hexp_one : Real.exp (-(255 / 256 : ℝ) * y) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hy)
    calc
      2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) ≤
          2500 * (1 + y ^ 8) * Real.exp (-(255 / 256 : ℝ) * y) := by
        gcongr
      _ = 2500 * (Real.exp (-(255 / 256 : ℝ) * y) +
          y ^ 8 * Real.exp (-(255 / 256 : ℝ) * y)) := by ring
      _ ≤ 2500 * (1 + (1 + (8 : ℕ).factorial / (255 / 256 : ℝ) ^ 8)) := by
        gcongr
      _ < 164000000 := by norm_num [Nat.factorial]

/-- The preceding one-variable estimate in the exact reciprocal-chart normalization. -/
@[category API, AMS 53]
private theorem reciprocalConformalDamping_bound (w : ℂ) :
    (‖w‖ ^ 2 + 10000) ^ 2 / 40000 * counterexampleTwoReciprocalDamping w <
      164000000 := by
  by_cases hw : w = 0
  · subst w
    simp [counterexampleTwoReciprocalDamping, counterexampleTwoReciprocalExponent]
    norm_num
  · let s := ‖w‖ ^ 2
    let y := (s / 10000) ^ ((1 : ℝ) / 8)
    have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr hw)
    have hy : 0 < y := Real.rpow_pos_of_pos (div_pos hs (by norm_num)) _
    have hy8 : y ^ 8 = s / 10000 := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hs.le (by norm_num))]
      norm_num
    have hyneg8 : y ^ (-(8 : ℝ)) = 10000 / s := by
      calc
        y ^ (-(8 : ℝ)) = (y ^ (8 : ℝ))⁻¹ := Real.rpow_neg hy.le (8 : ℝ)
        _ = (y ^ (8 : ℕ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast y 8)
        _ = 10000 / s := by rw [hy8, inv_div]
    have hψ : counterexampleTwoReciprocalExponent s =
        y * Real.exp (-(y ^ (-(8 : ℝ)))) := by
      rw [counterexampleTwoReciprocalExponent_of_pos hs, hyneg8]
      dsimp only [y]
      congr 2 ; ring
    have hbound := reciprocalMetricDamping_bound hy.le
    rw [counterexampleTwoReciprocalDamping]
    change (s + 10000) ^ 2 / 40000 *
      (10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)) < _
    rw [hψ]
    calc
      (s + 10000) ^ 2 / 40000 *
          (10000 / (s + 10000) * Real.exp (-(y * Real.exp (-y ^ (-(8 : ℝ)))))) =
          2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-y ^ (-(8 : ℝ))))) := by
        rw [hy8]
        field_simp [show s + 10000 ≠ 0 by positivity]
        ring
      _ < 164000000 := hbound

/-- The degree-one radial extension of a smooth function on the sphere is smooth away from the
origin. -/
@[category API, AMS 53]
private theorem radialExtension_contDiffOn_compl_of_contMDiff
    (h : sphere (0 : ℝ³) 1 → ℝ)
    (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h) :
    ContDiffOn ℝ ∞ (SphereSupport.radialExtension h) {0}ᶜ := by
  let U : TopologicalSpace.Opens ℝ³ := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hnorm : ContMDiff 𝓘(ℝ, ℝ³) 𝓘(ℝ, ℝ) ∞ (fun x : U ↦ ‖(x : ℝ³)‖) := by
    intro x
    exact (contDiffAt_norm ℝ x.property).contMDiffAt.comp x
      contMDiff_subtype_val.contMDiffAt
  have hnorm_ne : ∀ x : U, ‖(x : ℝ³)‖ ≠ 0 := fun x ↦ norm_ne_zero_iff.mpr x.property
  have hnorm_inv : ContMDiff 𝓘(ℝ, ℝ³) 𝓘(ℝ, ℝ) ∞
      (fun x : U ↦ ‖(x : ℝ³)‖⁻¹) := hnorm.inv₀ hnorm_ne
  have hnormalize_mem (x : U) : ‖(x : ℝ³)‖⁻¹ • (x : ℝ³) ∈ sphere (0 : ℝ³) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (hnorm_ne x)]
  let normalize : U → sphere (0 : ℝ³) 1 := fun x ↦
    ⟨‖(x : ℝ³)‖⁻¹ • (x : ℝ³), hnormalize_mem x⟩
  have hnormalize : ContMDiff 𝓘(ℝ, ℝ³) (𝓡 2) ∞ normalize := by
    exact (hnorm_inv.smul contMDiff_subtype_val).codRestrict_sphere hnormalize_mem
  have hradial : ContMDiff 𝓘(ℝ, ℝ³) 𝓘(ℝ, ℝ) ∞
      (fun x : U ↦ SphereSupport.radialExtension h (x : ℝ³)) := by
    apply (hnorm.mul (hsmooth.comp hnormalize)).congr
    intro x
    change SphereSupport.radialExtension h (x : ℝ³) =
      ‖(x : ℝ³)‖ * h (normalize x)
    have hx0 : (x : ℝ³) ≠ 0 := by
      intro hx
      apply x.property
      simpa only [Set.mem_singleton_iff] using hx
    rw [SphereSupport.radialExtension, dif_neg hx0]
  intro x hx
  let xU : U := ⟨x, hx⟩
  have hx_smooth : ContMDiffAt 𝓘(ℝ, ℝ³) 𝓘(ℝ, ℝ) ∞
      (SphereSupport.radialExtension h) x := by
    exact contMDiffAt_subtype_iff.mp (hradial.contMDiffAt :
      ContMDiffAt 𝓘(ℝ, ℝ³) 𝓘(ℝ, ℝ) ∞
        (fun y : U ↦ SphereSupport.radialExtension h (y : ℝ³)) xU)
  exact hx_smooth.contDiffAt.contDiffWithinAt

/-- The degree-one radial extension of a smooth function on the sphere is differentiable away
from the origin. This is applied only on the unit sphere below. -/
@[category API, AMS 53]
private theorem radialExtension_differentiableAt_of_contMDiff
    (h : sphere (0 : ℝ³) 1 → ℝ)
    (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (p : sphere (0 : ℝ³) 1) :
    DifferentiableAt ℝ (SphereSupport.radialExtension h) (p : ℝ³) := by
  exact (radialExtension_contDiffOn_compl_of_contMDiff h hsmooth
    (p : ℝ³) (ne_zero_of_mem_unit_sphere p)).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds (ne_zero_of_mem_unit_sphere p))

/-- The homogeneous extension of the explicit spherical function is differentiable at every
point of the unit sphere. -/
@[category API, AMS 53]
private theorem counterexampleTwoRadialExtension_differentiableAt
    (p : sphere (0 : ℝ³) 1) :
    DifferentiableAt ℝ
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) (p : ℝ³) := by
  exact radialExtension_differentiableAt_of_contMDiff counterexampleTwoSphereExtension
    (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
      counterexampleTwoSphereExtension_contMDiffAt_north) p

/-- The contact map obtained from the homogeneous extension of a smooth spherical function is
smooth. -/
@[category API, AMS 53]
private theorem homogeneousGradient_contMDiff_of_contMDiff
    (h : sphere (0 : ℝ³) 1 → ℝ)
    (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) ∞
      (SphereSupport.homogeneousGradient (SphereSupport.radialExtension h)) := by
  let H := SphereSupport.radialExtension h
  have hH : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff h hsmooth
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
    hH.fderiv_of_isOpen isOpen_compl_singleton (by simp)
  have hgradient : ContDiffOn ℝ ∞ (gradient H) {0}ᶜ := by
    simpa only [gradient] using
      (InnerProductSpace.toDual ℝ ℝ³).symm.contDiff.comp_contDiffOn hDf
  intro p
  have hp : (p : ℝ³) ∈ ({0}ᶜ : Set ℝ³) := ne_zero_of_mem_unit_sphere p
  have hp_gradient : ContDiffAt ℝ ∞ (gradient H) (p : ℝ³) :=
    (hgradient (p : ℝ³) hp).contDiffAt (isOpen_compl_singleton.mem_nhds hp)
  exact hp_gradient.contMDiffAt.comp p (contMDiff_coe_sphere p)

/-- The explicit homogeneous-gradient contact map is smooth. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_contMDiff :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) ∞
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)) := by
  exact homogeneousGradient_contMDiff_of_contMDiff counterexampleTwoSphereExtension
    (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
      counterexampleTwoSphereExtension_contMDiffAt_north)

/-- The first anti-holomorphic derivative, in the normalization for which the repository's
`traceFreeHessian` is four times its second iterate. -/
private noncomputable def complexBarDeriv (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  ((fderiv ℝ u w 1 : ℂ) + (fderiv ℝ u w Complex.I : ℂ) * Complex.I) / 2

/-- The trace-free spherical Hessian in a stereographic chart whose metric denominator is
`‖w‖² + a`. Its vanishing is the coordinate form of the umbilic equation. -/
private noncomputable def sphericalTraceFreeHessian (a : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  traceFreeHessian u w + 8 * w / (‖w‖ ^ 2 + a) * complexBarDeriv u w

/-- The Euclidean chart Laplacian, encoded using the same second Fréchet derivative as the
trace-free Hessian. -/
private noncomputable def chartLaplacian (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  let H := fderiv ℝ (fun z ↦ fderiv ℝ u z) w
  H 1 1 + H Complex.I Complex.I

/-- In reciprocal coordinates, the homogeneous gradient is the support value in the radial
direction plus the metric-dual of the first derivative in the tangent direction. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_reciprocalSphereChart (w : ℂ) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let dρ := fderiv ℝ
      (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w
    F (counterexampleTwoReciprocalSphereChart w) =
      counterexampleTwoReciprocal w • (counterexampleTwoReciprocalSphereChart w : ℝ³) +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 20000) •
          dρ (complexBarDeriv counterexampleTwoReciprocal w) := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ w
  let p := counterexampleTwoReciprocalSphereChart w
  let G : ℝ³ := counterexampleTwoReciprocal w • (p : ℝ³) +
    ((‖w‖ ^ 2 + 10000) ^ 2 / 20000) •
      dρ (complexBarDeriv counterexampleTwoReciprocal w)
  have hρdiff : Differentiable ℝ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleTwoReciprocalSphereChart_contMDiff).contDiff
      |>.differentiable (by simp)
  have hdρrange : dρ.range = (ℝ ∙ (p : ℝ³))ᗮ := by
    simpa only [dρ, ρ, p] using range_fderiv_counterexampleTwoReciprocalSphereChart w
  have hdρorth (v : ℂ) : inner ℝ (dρ v) (p : ℝ³) = 0 := by
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_left, ← hdρrange]
    exact ⟨v, rfl⟩
  have hHdiff : DifferentiableAt ℝ H (p : ℝ³) :=
    counterexampleTwoRadialExtension_differentiableAt p
  have hcontact : inner ℝ (F p) (p : ℝ³) = counterexampleTwoReciprocal w := by
    calc
      inner ℝ (F p) (p : ℝ³) = H p :=
        SphereSupport.inner_homogeneousGradient H p hHdiff
          (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
      _ = counterexampleTwoReciprocal w := by
        dsimp only [H]
        rw [SphereSupport.radialExtension_coe,
          counterexampleTwoSphereExtension_reciprocalSphereChart]
  have hdifferentiate (v : ℂ) :
      fderiv ℝ counterexampleTwoReciprocal w v =
        fderiv ℝ H (p : ℝ³) (dρ v) := by
    have hcomp := hHdiff.hasFDerivAt.comp w hρdiff.differentiableAt.hasFDerivAt
    have heq : H ∘ ρ = counterexampleTwoReciprocal := by
      funext z
      dsimp only [Function.comp_apply, H, ρ]
      rw [SphereSupport.radialExtension_coe,
        counterexampleTwoSphereExtension_reciprocalSphereChart]
    rw [heq] at hcomp
    exact congr($hcomp.fderiv v)
  have hfirst (v : ℂ) : fderiv ℝ counterexampleTwoReciprocal w v =
      2 * inner ℝ (complexBarDeriv counterexampleTwoReciprocal w) v := by
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hv, map_add, map_smul, map_smul, complexBarDeriv]
    simp only [smul_eq_mul]
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    norm_num
    ring
  have hGcontact : inner ℝ G (p : ℝ³) = counterexampleTwoReciprocal w := by
    dsimp only [G]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hdρorth, mul_zero, add_zero, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere p]
    ring
  have htangent (v : ℂ) : inner ℝ (F p - G) (dρ v) = 0 := by
    dsimp only [F, SphereSupport.homogeneousGradient]
    rw [inner_sub_left, inner_gradient_left hHdiff, ← hdifferentiate v, hfirst]
    have hmetric := (counterexampleTwoReciprocalSphereChart_conformal w
      (complexBarDeriv counterexampleTwoReciprocal w) v).1
    change inner ℝ (dρ (complexBarDeriv counterexampleTwoReciprocal w)) (dρ v) =
      40000 / (‖w‖ ^ 2 + 10000) ^ 2 *
        inner ℝ (complexBarDeriv counterexampleTwoReciprocal w) v at hmetric
    dsimp only [G]
    have hporth : inner ℝ (p : ℝ³) (dρ v) = 0 := by
      rw [real_inner_comm, hdρorth]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hporth,
      mul_zero, zero_add, hmetric]
    field_simp
    ring
  have hradial : inner ℝ (F p - G) (p : ℝ³) = 0 := by
    rw [inner_sub_left, hcontact, hGcontact, sub_self]
  have hdmem : F p - G ∈ dρ.range := by
    rw [hdρrange, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hradial
  obtain ⟨v, hv⟩ := hdmem
  have hzero := htangent v
  rw [← hv] at hzero
  change inner ℝ (dρ v) (dρ v) = 0 at hzero
  rw [real_inner_self_eq_norm_sq] at hzero
  have hdρzero : dρ v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have hdiffzero : F p - G = 0 := by
    have hzero' : (0 : ℝ³) = F p - G := by simpa [hdρzero] using hv
    exact hzero'.symm
  exact sub_eq_zero.mp hdiffzero

/-- The real Fréchet derivative expressed through the complex bar derivative. -/
@[category API, AMS 53]
private theorem fderiv_eq_two_inner_complexBarDeriv (u : ℂ → ℝ) (w v : ℂ) :
    fderiv ℝ u w v = 2 * inner ℝ (complexBarDeriv u w) v := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp only [complexBarDeriv, smul_eq_mul]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_apply]
  norm_num
  ring

/-- The derivative of the complex bar derivative in terms of the two Hessian encodings. -/
@[category API, AMS 53]
private theorem complexBarDeriv_fderiv_eq (u : ℂ → ℝ) (hu : ContDiff ℝ ∞ u) (w v : ℂ) :
    fderiv ℝ (complexBarDeriv u) w v =
      ((((chartLaplacian u w : ℝ) : ℂ) * v +
        traceFreeHessian u w * star v) / 4) := by
  let M := fderiv ℝ (fun z ↦ fderiv ℝ u z) w
  have hDu : DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z) w :=
    (hu.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero w
  have hM (t : ℂ) :
      fderiv ℝ (fun z ↦ (fderiv ℝ u z t : ℂ)) w v = (M v t : ℂ) := by
    have ht := hDu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) t)
    have hcast := Complex.ofRealCLM.hasFDerivAt.comp w ht
    simpa [M] using congr($hcast.fderiv v)
  have hcomponentDiff (t : ℂ) :
      DifferentiableAt ℝ (fun z ↦ (fderiv ℝ u z t : ℂ)) w := by
    have ht := hDu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) t)
    exact (Complex.ofRealCLM.hasFDerivAt.comp w ht).differentiableAt
  rw [show complexBarDeriv u = fun z ↦
    ((fderiv ℝ u z 1 : ℂ) + (fderiv ℝ u z Complex.I : ℂ) * Complex.I) / 2 by rfl]
  simp only [div_eq_mul_inv]
  have hwhole := ((hcomponentDiff 1).hasFDerivAt.add
    ((hcomponentDiff Complex.I).hasFDerivAt.mul_const Complex.I)).mul_const (2 : ℂ)⁻¹
  have hwhole' := hwhole.fderiv
  simp only [Pi.add_apply] at hwhole'
  rw [hwhole']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  rw [hM, hM]
  · have hsymm (a b : ℂ) : M a b = M b a := by
      dsimp only [M]
      exact hu.contDiffAt.isSymmSndFDerivAt
        (by
          simpa only [minSmoothness_of_isRCLikeNormedField] using
            (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
              exact WithTop.coe_le_coe.mpr le_top)) a b
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp
    have hMv1 : M v 1 = v.re * M 1 1 + v.im * M 1 Complex.I := by
      nth_rw 1 [hv]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsymm Complex.I 1]
    have hMvI : M v Complex.I =
        v.re * M 1 Complex.I + v.im * M Complex.I Complex.I := by
      nth_rw 1 [hv]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hMv1, hMvI, chartLaplacian, traceFreeHessian]
    dsimp only [M]
    simp only [smul_eq_mul]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The complex-coordinate algebra in the reciprocal radius formula. -/
@[category API, AMS 53]
private theorem reciprocal_radius_source_vector (u : ℂ → ℝ) (w v : ℂ) (D : ℝ) (g : ℂ)
    (hDdef : D = ‖w‖ ^ 2 + 10000) (hgdef : g = complexBarDeriv u w) :
        (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
            (D / 5000 * inner ℝ w v) • g +
            (D ^ 2 / 20000) •
              ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                  inner ℝ v g • w) +
                ((((chartLaplacian u w : ℝ) : ℂ) * v +
                    traceFreeHessian u w * star v) / 4)) =
          (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
            (D ^ 2 / 80000) •
              (((chartLaplacian u w : ℝ) : ℂ) * v +
                sphericalTraceFreeHessian 10000 u w * star v) := by
  have hcomplex : inner ℝ w v • g - inner ℝ w g • v +
      inner ℝ v g • w = w * g * star v := by
    apply Complex.ext <;> simp [Complex.inner, add_mul] <;> ring
  rw [hgdef] at hcomplex
  have hD : D ≠ 0 := by
    rw [hDdef]
    positivity
  have hDcast : (((‖w‖ : ℝ) : ℂ) ^ 2) + ((10000 : ℝ) : ℂ) = (D : ℂ) := by
    rw [hDdef]
    norm_cast
  have herrorVector :
      (D / 5000 * inner ℝ w v) • g +
          (D ^ 2 / 20000) •
            ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
              inner ℝ v g • w)) =
        (D / 10000) • (inner ℝ w v • g - inner ℝ w g • v +
          inner ℝ v g • w) := by
    have htwice : D / 5000 = 2 * (D / 10000) := by ring
    have hnegative : (D ^ 2 / 20000) * (-2 / D) = -(D / 10000) := by
      field_simp [hD]
      ring
    simp only [smul_smul, htwice, hnegative]
    module
  calc
    (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D / 5000 * inner ℝ w v) • g +
          (D ^ 2 / 20000) •
            ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                inner ℝ v g • w) +
              ((((chartLaplacian u w : ℝ) : ℂ) * v +
                traceFreeHessian u w * star v) / 4)) =
        (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          ((D / 5000 * inner ℝ w v) • g +
            (D ^ 2 / 20000) •
              ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                inner ℝ v g • w))) +
          (D ^ 2 / 20000) •
            ((((chartLaplacian u w : ℝ) : ℂ) * v +
              traceFreeHessian u w * star v) / 4) := by module
    _ = (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D / 10000) • (inner ℝ w v • g - inner ℝ w g • v +
            inner ℝ v g • w) +
          (D ^ 2 / 20000) •
            ((((chartLaplacian u w : ℝ) : ℂ) * v +
              traceFreeHessian u w * star v) / 4) := by rw [herrorVector]
    _ = _ := by
      rw [hgdef, hcomplex, sphericalTraceFreeHessian]
      rw [hDcast]
      apply Complex.ext <;> simp [-Complex.ofReal_pow] <;>
        field_simp [hD] <;> ring

/-- The second derivative of the reciprocal spherical chart in ambient coordinates. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalSphereChart_second_fderiv (w a b : ℂ) :
    fderiv ℝ (fun z ↦ fderiv ℝ
      (fun y : ℂ ↦ (counterexampleTwoReciprocalSphereChart y : ℝ³)) z) w a b =
        fderiv ℝ (fun y : ℂ ↦ (counterexampleTwoReciprocalSphereChart y : ℝ³)) w
            ((-2 / (‖w‖ ^ 2 + 10000)) •
              (inner ℝ w a • b + inner ℝ w b • a - inner ℝ a b • w)) -
          (40000 / (‖w‖ ^ 2 + 10000) ^ 2 * inner ℝ a b) •
            (counterexampleTwoReciprocalSphereChart w : ℝ³) := by
  let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ w
  let D : ℝ := ‖w‖ ^ 2 + 10000
  change fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w a b =
    dρ ((-2 / D) • (inner ℝ w a • b + inner ℝ w b • a - inner ℝ a b • w)) -
      (40000 / D ^ 2 * inner ℝ a b) • (ρ w)
  have hρsmooth : ContDiff ℝ ∞ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleTwoReciprocalSphereChart_contMDiff).contDiff
  have hDρ : DifferentiableAt ℝ (fun z ↦ fderiv ℝ ρ z) w := by
    exact (hρsmooth.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero w
  have heval : fderiv ℝ (fun z ↦ fderiv ℝ ρ z b) w a =
      fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w a b := by
    have ht := hDρ.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) b)
    simpa using congr($ht.fderiv a)
  rw [← heval]
  have heq : (fun z ↦ fderiv ℝ ρ z b) = fun z : ℂ ↦
      (200 / (‖z‖ ^ 2 + 10000)) • (counterexampleTwoTangentEquiv b : ℝ³) -
        (400 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
          (counterexampleTwoTangentEquiv z : ℝ³) -
        (40000 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
          (counterexampleNorthPole : ℝ³) := by
    funext z
    exact counterexampleTwoReciprocalSphereChart_fderiv_apply z b
  rw [heq]
  let S : ℂ → ℝ := fun z ↦ ‖z‖ ^ 2 + 10000
  let I : ℂ → ℝ := fun z ↦ inner ℝ z b
  let T : ℂ →L[ℝ] ℝ³ :=
    (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hS : HasFDerivAt S (2 • innerSL ℝ w) w := by
    dsimp only [S]
    simpa only [two_smul] using
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const 10000
  have hI : HasFDerivAt I (innerSL ℝ b) w := by
    dsimp only [I]
    simpa [real_inner_comm] using (innerSL ℝ b).hasFDerivAt
  have hq : HasFDerivAt (fun z ↦ (S z)⁻¹)
      (-((S w) ^ 2)⁻¹ • (2 • innerSL ℝ w)) w := by
    convert (hasDerivAt_inv (by dsimp only [S]; positivity)).hasFDerivAt.comp w hS using 1 ;
      ext x ; simp ; ring
  have hT : HasFDerivAt
      (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³)) T w := T.hasFDerivAt
  have hR := hI.mul (hq.pow 2)
  have hE := (((hq.const_mul 200).smul_const
    (counterexampleTwoTangentEquiv b : ℝ³)).sub
      ((hR.const_mul 400).smul hT)).sub
        ((hR.const_mul 40000).smul_const (counterexampleNorthPole : ℝ³))
  have hsource :
      (fun z : ℂ ↦
        (200 / (‖z‖ ^ 2 + 10000)) • (counterexampleTwoTangentEquiv b : ℝ³) -
          (400 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
            (counterexampleTwoTangentEquiv z : ℝ³) -
          (40000 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
            (counterexampleNorthPole : ℝ³)) =
        fun z ↦
          (200 * (S z)⁻¹) • (counterexampleTwoTangentEquiv b : ℝ³) -
            (400 * (I z * (S z)⁻¹ ^ 2)) •
              (counterexampleTwoTangentEquiv z : ℝ³) -
            (40000 * (I z * (S z)⁻¹ ^ 2)) •
              (counterexampleNorthPole : ℝ³) := by
    funext z
    dsimp only [S, I]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [hsource]
  have hfun :
      (fun z : ℂ ↦
        (200 * (S z)⁻¹) • (counterexampleTwoTangentEquiv b : ℝ³) -
          (400 * (I z * (S z)⁻¹ ^ 2)) • (counterexampleTwoTangentEquiv z : ℝ³) -
          (40000 * (I z * (S z)⁻¹ ^ 2)) • (counterexampleNorthPole : ℝ³)) =
        (((fun z : ℂ ↦
            (200 * (S z)⁻¹) • (counterexampleTwoTangentEquiv b : ℝ³)) -
          ((fun z : ℂ ↦ 400 * (I * fun x ↦ (S x)⁻¹ ^ 2) z) •
            fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³))) -
          fun z : ℂ ↦
            (40000 * (I * fun x ↦ (S x)⁻¹ ^ 2) z) •
              (counterexampleNorthPole : ℝ³)) := by
    funext z
    rfl
  rw [hfun, hE.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  dsimp only [S, I, T]
  dsimp only [ρ]
  rw [counterexampleTwoReciprocalSphereChart_coe]
  dsimp only [D, dρ]
  rw [counterexampleTwoReciprocalSphereChart_fderiv_apply]
  have hTa : ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap) a =
        (counterexampleTwoTangentEquiv a : ℝ³) := rfl
  rw [hTa]
  simp only [map_add, map_sub, map_smul, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, smul_add, smul_sub, smul_smul, div_eq_mul_inv,
    ← inv_pow, Nat.reduceSub, pow_one, inner_add_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, smul_eq_mul, Pi.mul_apply]
  rw [real_inner_comm b a]
  have hdenOrder : ‖w‖ ^ 2 + 10000 = 10000 + ‖w‖ ^ 2 := by ring
  rw [hdenOrder]
  have hden : 10000 + ‖w‖ ^ 2 ≠ 0 := by positivity
  have hcancel (X Y c k : ℝ) :
      ‖w‖ ^ 2 * X * (10000 + ‖w‖ ^ 2)⁻¹ * Y * k - ‖w‖ ^ 2 * c +
            (X * (10000 + ‖w‖ ^ 2)⁻¹ * Y * (10000 * k) - c * 10000) =
          -(‖w‖ ^ 2 * c) + (X * Y * k - c * 10000) := by
    calc
      _ = ((10000 + ‖w‖ ^ 2) * (10000 + ‖w‖ ^ 2)⁻¹) * X * Y * k -
            ‖w‖ ^ 2 * c - c * 10000 := by ring
      _ = X * Y * k - ‖w‖ ^ 2 * c - c * 10000 := by
        rw [mul_inv_cancel₀ hden]
        ring
      _ = _ := by ring
  have hcancelFour :
      ‖w‖ ^ 2 * inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 4 -
            ‖w‖ ^ 2 * inner ℝ b a +
            (inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 40000 -
              inner ℝ b a * 10000) =
          -(‖w‖ ^ 2 * inner ℝ b a) +
            (inner ℝ w b * inner ℝ w a * 4 - inner ℝ b a * 10000) := by
    convert hcancel (inner ℝ w b) (inner ℝ w a) (inner ℝ b a) 4 using 1
    all_goals ring
  have hcancelSixteenHundred :
      ‖w‖ ^ 2 * inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 1600 -
            ‖w‖ ^ 2 * inner ℝ b a * 400 +
            (inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 16000000 -
              inner ℝ b a * 4000000) =
          -(‖w‖ ^ 2 * inner ℝ b a * 400) +
            (inner ℝ w b * inner ℝ w a * 1600 - inner ℝ b a * 4000000) := by
    convert hcancel (inner ℝ w b) (inner ℝ w a) (inner ℝ b a * 400) 1600 using 1
    all_goals ring
  match_scalars <;> field_simp [hden] <;> try ring
  all_goals assumption

/- The product-rule part of the radius computation is kept separate from the subsequent
coordinate algebra.  Apart from making the two mathematical steps explicit, this prevents
the elaborator from retaining all of the smoothness witnesses while normalizing the final
complex expression. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_reciprocalSphereChart_fderiv
    (w v : ℂ) :
    let u := counterexampleTwoReciprocal
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
    let D : ℝ := ‖w‖ ^ 2 + 10000
    let g : ℂ := complexBarDeriv u w
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v =
      (fderiv ℝ u w v) • ρ w + u w • fderiv ℝ ρ w v +
        (4 * D / 20000 * inner ℝ w v) • fderiv ℝ ρ w g +
          (D ^ 2 / 20000) •
            (fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w v g +
              fderiv ℝ ρ w (fderiv ℝ (complexBarDeriv u) w v)) := by
  dsimp only
  let u := counterexampleTwoReciprocal
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let D : ℝ := ‖w‖ ^ 2 + 10000
  let g : ℂ := complexBarDeriv u w
  have hu : ContDiff ℝ ∞ u := counterexampleTwoReciprocal_contDiff
  have hρsmooth : ContDiff ℝ ∞ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleTwoReciprocalSphereChart_contMDiff).contDiff
  have hρ : Differentiable ℝ ρ := hρsmooth.differentiable (by simp)
  have hFchart : (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) =
      fun z : ℂ ↦ u z • ρ z + ((‖z‖ ^ 2 + 10000) ^ 2 / 20000) •
        fderiv ℝ ρ z (complexBarDeriv u z) := by
    funext z
    exact counterexampleTwoHomogeneousGradient_reciprocalSphereChart z
  have hgdiff : DifferentiableAt ℝ (complexBarDeriv u) w := by
    have hDu : DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z) w :=
      (hu.fderiv_right (m := 1)
        (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top)).differentiable
        one_ne_zero w
    have hcomponent (t : ℂ) :
        DifferentiableAt ℝ (fun z ↦ (fderiv ℝ u z t : ℂ)) w := by
      have ht := hDu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) t)
      exact (Complex.ofRealCLM.hasFDerivAt.comp w ht).differentiableAt
    change DifferentiableAt ℝ (fun z ↦
      ((fderiv ℝ u z 1 : ℂ) + (fderiv ℝ u z Complex.I : ℂ) * Complex.I) / 2) w
    simpa only [div_eq_mul_inv] using
      (((hcomponent 1).add
        ((hcomponent Complex.I).mul_const Complex.I)).mul_const (2 : ℂ)⁻¹)
  have hscale : HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 + 10000) ^ 2 / 20000)
      (((4 * D / 20000) • innerSL ℝ w)) w := by
    convert (((hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const 10000).pow 2).mul_const
      (20000 : ℝ)⁻¹ using 1
    all_goals
      ext x
      simp [D, div_eq_mul_inv]
      ring
  have hDρdiff : DifferentiableAt ℝ (fun z ↦ fderiv ℝ ρ z) w :=
    (hρsmooth.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero w
  have hdnApply := hDρdiff.hasFDerivAt.clm_apply hgdiff.hasFDerivAt
  have huDiff : DifferentiableAt ℝ u w := hu.differentiable (by simp) w
  have hρDiff : DifferentiableAt ℝ ρ w := hρ w
  have hscaleDiff := hscale.differentiableAt
  have hdnDiff := hdnApply.differentiableAt
  change fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v =
    (fderiv ℝ u w v) • ρ w + u w • fderiv ℝ ρ w v +
      (4 * D / 20000 * inner ℝ w v) • fderiv ℝ ρ w g +
        (D ^ 2 / 20000) •
          (fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w v g +
            fderiv ℝ ρ w (fderiv ℝ (complexBarDeriv u) w v))
  rw [hFchart]
  change fderiv ℝ ((fun z : ℂ ↦ u z • ρ z) + fun z : ℂ ↦
      ((‖z‖ ^ 2 + 10000) ^ 2 / 20000) •
        fderiv ℝ ρ z (complexBarDeriv u z)) w v = _
  change fderiv ℝ (fun z : ℂ ↦
      (u • ρ) z +
        (((fun y : ℂ ↦ (‖y‖ ^ 2 + 10000) ^ 2 / 20000) •
          fun y : ℂ ↦ fderiv ℝ ρ y (complexBarDeriv u y)) z)) w v = _
  rw [fderiv_fun_add (huDiff.smul hρDiff) (hscaleDiff.smul hdnDiff)]
  change (fderiv ℝ (fun y ↦ u y • ρ y) w +
    fderiv ℝ (fun y : ℂ ↦ ((‖y‖ ^ 2 + 10000) ^ 2 / 20000) •
      fderiv ℝ ρ y (complexBarDeriv u y)) w) v = _
  rw [fderiv_fun_smul huDiff hρDiff, fderiv_fun_smul hscaleDiff hdnDiff]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [hscale.fderiv, hdnApply.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  dsimp only [D, g]
  match_scalars <;> try ring
  change (2 + ‖w‖ ^ 2 * (1 / 5000)) * inner ℝ w v =
    ‖w‖ ^ 2 * inner ℝ w v * (1 / 5000) + inner ℝ w v * 2
  ring

/-- Exact radius-tensor formula in the reciprocal chart. The complex-linear coefficient is
the chart Laplacian, while the anti-linear coefficient is the spherical trace-free Hessian. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocal_radius_formula (w v : ℂ) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let ρ := fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
    let dρ := fderiv ℝ ρ w
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v -
        (10 ^ 10 : ℝ) • dρ v =
      dρ ((((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ) * v) +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 80000 : ℝ) •
          (((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ) * v +
            sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w * star v)) := by
  let u := counterexampleTwoReciprocal
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ w
  let D : ℝ := ‖w‖ ^ 2 + 10000
  let g : ℂ := complexBarDeriv u w
  have hu : ContDiff ℝ ∞ u := counterexampleTwoReciprocal_contDiff
  have hdu : fderiv ℝ u w v = 2 * inner ℝ g v := by
    exact fderiv_eq_two_inner_complexBarDeriv u w v
  have hdg : fderiv ℝ (complexBarDeriv u) w v =
      ((((chartLaplacian u w : ℝ) : ℂ) * v +
        traceFreeHessian u w * star v) / 4) := by
    exact complexBarDeriv_fderiv_eq u hu w v
  have hsecond (a b : ℂ) :
      fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w a b =
        dρ ((-2 / D) • (inner ℝ w a • b + inner ℝ w b • a -
          inner ℝ a b • w)) -
          (40000 / D ^ 2 * inner ℝ a b) • (ρ w) := by
    simpa only [ρ, dρ, D] using
      counterexampleTwoReciprocalSphereChart_second_fderiv w a b
  change fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v -
      (10 ^ 10 : ℝ) • dρ v =
    dρ ((((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
      (D ^ 2 / 80000) •
        (((chartLaplacian u w : ℝ) : ℂ) * v +
          sphericalTraceFreeHessian 10000 u w * star v))
  rw [counterexampleTwoHomogeneousGradient_reciprocalSphereChart_fderiv]
  rw [hdu]
  rw [hsecond v g, hdg]
  have hD : D ≠ 0 := by
    dsimp only [D]
    positivity
  have hsourceVector :
      (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D / 5000 * inner ℝ w v) • g +
          (D ^ 2 / 20000) •
            ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                inner ℝ v g • w) +
              ((((chartLaplacian u w : ℝ) : ℂ) * v +
                  traceFreeHessian u w * star v) / 4)) =
        (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D ^ 2 / 80000) •
            (((chartLaplacian u w : ℝ) : ℂ) * v +
              sphericalTraceFreeHessian 10000 u w * star v) := by
    exact reciprocal_radius_source_vector u w v D g rfl rfl
  rw [← hsourceVector]
  rw [show (((u w - 10 ^ 10 : ℝ) : ℂ) * v) =
      (u w - 10 ^ 10 : ℝ) • v by exact Complex.real_smul.symm]
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul]
  rw [show ‖w‖ ^ 2 + 10000 = D by rfl]
  have hscaleDerivative : 4 * D / 20000 * inner ℝ w v =
        D / 5000 * inner ℝ w v := by ring
  rw [hscaleDerivative]
  have hradialScalar : (D ^ 2 / 20000) *
        (40000 / D ^ 2 * inner ℝ v g) = 2 * inner ℝ g v := by
    rw [real_inner_comm v g]
    field_simp [hD]
    ring
  rw [hradialScalar]
  rw [real_inner_comm g v]
  module

/-- Product rule for the complex encoding of the trace-free Hessian. -/
@[category API, AMS 53]
private theorem traceFreeHessian_mul (f g : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : ℂ) :
    traceFreeHessian (fun z ↦ f z * g z) w =
      (f w : ℂ) * traceFreeHessian g w +
        (g w : ℂ) * traceFreeHessian f w +
          8 * complexBarDeriv f w * complexBarDeriv g w := by
  have hf0 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg0 : Differentiable ℝ g := hg.differentiable (by simp)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hDg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hgradient : fderiv ℝ (fun z ↦ f z * g z) =
      fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    funext z
    exact fderiv_fun_mul (hf0 z) (hg0 z)
  have hfun : (fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z) =
      f • fderiv ℝ g + g • fderiv ℝ f := rfl
  have hsum : fderiv ℝ (f • fderiv ℝ g + g • fderiv ℝ f) w =
      fderiv ℝ (f • fderiv ℝ g) w + fderiv ℝ (g • fderiv ℝ f) w := by
    change fderiv ℝ (fun y ↦ (f • fderiv ℝ g) y + (g • fderiv ℝ f) y) w = _
    exact fderiv_fun_add ((hf0.smul hDg) w) ((hg0.smul hDf) w)
  have hfprod : fderiv ℝ (f • fderiv ℝ g) w =
      f w • fderiv ℝ (fderiv ℝ g) w + (fderiv ℝ f w).smulRight (fderiv ℝ g w) := by
    change fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) w = _
    exact fderiv_fun_smul (hf0 w) (hDg w)
  have hgprod : fderiv ℝ (g • fderiv ℝ f) w =
      g w • fderiv ℝ (fderiv ℝ f) w + (fderiv ℝ g w).smulRight (fderiv ℝ f w) := by
    change fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) w = _
    exact fderiv_fun_smul (hg0 w) (hDf w)
  rw [traceFreeHessian, hgradient, hfun, hsum,
    hfprod, hgprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [traceFreeHessian, traceFreeHessian, complexBarDeriv, complexBarDeriv]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Product rule for the Euclidean chart Laplacian. -/
@[category API, AMS 53]
private theorem chartLaplacian_mul (f g : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : ℂ) :
    chartLaplacian (fun z ↦ f z * g z) w =
      f w * chartLaplacian g w + g w * chartLaplacian f w +
        2 * (fderiv ℝ f w 1 * fderiv ℝ g w 1 +
          fderiv ℝ f w Complex.I * fderiv ℝ g w Complex.I) := by
  have hf0 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg0 : Differentiable ℝ g := hg.differentiable (by simp)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hDg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hgradient : fderiv ℝ (fun z ↦ f z * g z) =
      fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    funext z
    exact fderiv_fun_mul (hf0 z) (hg0 z)
  have hfun : (fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z) =
      f • fderiv ℝ g + g • fderiv ℝ f := rfl
  have hsum : fderiv ℝ (f • fderiv ℝ g + g • fderiv ℝ f) w =
      fderiv ℝ (f • fderiv ℝ g) w + fderiv ℝ (g • fderiv ℝ f) w := by
    change fderiv ℝ (fun y ↦ (f • fderiv ℝ g) y + (g • fderiv ℝ f) y) w = _
    exact fderiv_fun_add ((hf0.smul hDg) w) ((hg0.smul hDf) w)
  have hfprod : fderiv ℝ (f • fderiv ℝ g) w =
      f w • fderiv ℝ (fderiv ℝ g) w + (fderiv ℝ f w).smulRight (fderiv ℝ g w) := by
    change fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) w = _
    exact fderiv_fun_smul (hf0 w) (hDg w)
  have hgprod : fderiv ℝ (g • fderiv ℝ f) w =
      g w • fderiv ℝ (fderiv ℝ f) w + (fderiv ℝ g w).smulRight (fderiv ℝ f w) := by
    change fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) w = _
    exact fderiv_fun_smul (hg0 w) (hDf w)
  rw [chartLaplacian, hgradient, hfun, hsum,
    hfprod, hgprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [chartLaplacian, chartLaplacian]
  ring

/-- Product rule for the first anti-holomorphic derivative. -/
@[category API, AMS 53]
private theorem complexBarDeriv_mul (f g : ℂ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (w : ℂ) :
    complexBarDeriv (fun z ↦ f z * g z) w =
      (f w : ℂ) * complexBarDeriv g w + (g w : ℂ) * complexBarDeriv f w := by
  rw [complexBarDeriv, fderiv_fun_mul (hf w) (hg w)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [complexBarDeriv, complexBarDeriv]
  push_cast
  ring

/-- Adding a constant does not change the first anti-holomorphic derivative. -/
@[category API, AMS 53]
private theorem complexBarDeriv_const_add (c : ℝ) (f : ℂ → ℝ)
    (hf : Differentiable ℝ f) (w : ℂ) :
    complexBarDeriv (fun z ↦ c + f z) w = complexBarDeriv f w := by
  have hsum := (hasFDerivAt_const (x := w) c).add (hf w).hasFDerivAt
  rw [complexBarDeriv]
  change (↑((fderiv ℝ (((fun _ : ℂ ↦ c) + f)) w) 1) +
    ↑((fderiv ℝ (((fun _ : ℂ ↦ c) + f)) w) Complex.I) * Complex.I) / 2 = _
  rw [hsum.fderiv]
  simp [complexBarDeriv]

/-- Adding a constant does not change the trace-free Hessian. -/
@[category API, AMS 53]
private theorem traceFreeHessian_const_add (c : ℝ) (f : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : ℂ) :
    traceFreeHessian (fun z ↦ c + f z) w = traceFreeHessian f w := by
  have hgradient : fderiv ℝ (fun z ↦ c + f z) = fderiv ℝ f := by
    funext z
    change fderiv ℝ (((fun _ : ℂ ↦ c) + f)) z = _
    rw [((hasFDerivAt_const (x := z) c).add
      (hf.differentiable (by simp) z).hasFDerivAt).fderiv]
    simp
  rw [traceFreeHessian, hgradient]
  rfl

/-- Adding a constant does not change the chart Laplacian. -/
@[category API, AMS 53]
private theorem chartLaplacian_const_add (c : ℝ) (f : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : ℂ) :
    chartLaplacian (fun z ↦ c + f z) w = chartLaplacian f w := by
  have hgradient : fderiv ℝ (fun z ↦ c + f z) = fderiv ℝ f := by
    funext z
    change fderiv ℝ (((fun _ : ℂ ↦ c) + f)) z = _
    rw [((hasFDerivAt_const (x := z) c).add
      (hf.differentiable (by simp) z).hasFDerivAt).fderiv]
    simp
  rw [chartLaplacian, hgradient]
  rfl

/-- The first anti-holomorphic derivative of a radial scalar function. -/
@[category API, AMS 53]
private theorem complexBarDeriv_comp_norm_sq (β : ℝ → ℝ) (w : ℂ)
    (hβ : DifferentiableAt ℝ β (‖w‖ ^ 2)) :
    complexBarDeriv (fun z : ℂ ↦ β (‖z‖ ^ 2)) w =
      ((deriv β (‖w‖ ^ 2) : ℝ) : ℂ) * w := by
  have hre : HasFDerivAt (fun z : ℂ ↦ z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ ↦ z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hs : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    convert (hre.pow 2).add (him.pow 2) using 1
    · funext z
      simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm z
    · ext v
      simp
  have hcomp := hβ.hasDerivAt.hasFDerivAt.comp w hs
  rw [complexBarDeriv]
  change (↑((fderiv ℝ (β ∘ fun z : ℂ ↦ ‖z‖ ^ 2) w) 1) +
    ↑((fderiv ℝ (β ∘ fun z : ℂ ↦ ‖z‖ ^ 2) w) Complex.I) * Complex.I) / 2 = _
  rw [hcomp.fderiv]
  apply Complex.ext <;> simp <;> ring

/-- The trace-free Hessian of a radial scalar function. -/
@[category API, AMS 53]
private theorem traceFreeHessian_comp_norm_sq (β : ℝ → ℝ) (w : ℂ)
    (hβ : ContDiffAt ℝ 2 β (‖w‖ ^ 2)) :
    traceFreeHessian (fun z : ℂ ↦ β (‖z‖ ^ 2)) w =
      4 * ((deriv (fun x ↦ deriv β x) (‖w‖ ^ 2) : ℝ) : ℂ) * w ^ 2 := by
  have hs (z : ℂ) : HasFDerivAt (fun y : ℂ ↦ ‖y‖ ^ 2)
      ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) z := by
    have hre : HasFDerivAt (fun y : ℂ ↦ y.re) Complex.reCLM z :=
      Complex.reCLM.hasFDerivAt
    have him : HasFDerivAt (fun y : ℂ ↦ y.im) Complex.imCLM z :=
      Complex.imCLM.hasFDerivAt
    convert (hre.pow 2).add (him.pow 2) using 1
    · funext y
      simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm y
    · ext v
      simp
  have hβnear : ∀ᶠ z in nhds w, ContDiffAt ℝ 2 β (‖z‖ ^ 2) :=
    (contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun z : ℂ ↦ ‖z‖ ^ 2)).continuous.continuousAt.tendsto
      (hβ.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞))
  have hgradient : fderiv ℝ (fun z : ℂ ↦ β (‖z‖ ^ 2)) =ᶠ[nhds w] fun z ↦
      deriv β (‖z‖ ^ 2) •
        ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) := by
    filter_upwards [hβnear] with z hz
    have hcomp :=
      (hz.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp z (hs z)
    convert hcomp.fderiv using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hderivβ : ContDiffAt ℝ 1 (fun x ↦ deriv β x) (‖w‖ ^ 2) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      ((hβ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have hscalar : HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2))
      (deriv (fun x ↦ deriv β x) (‖w‖ ^ 2) •
        ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
    have hcomp :=
      (hderivβ.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp w (hs w)
    convert hcomp using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hre : HasFDerivAt (fun z : ℂ ↦ z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ ↦ z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hmatrix := ((hre.const_mul 2).smul_const Complex.reCLM).add
    ((him.const_mul 2).smul_const Complex.imCLM)
  have hsecond := hscalar.smul hmatrix
  change HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2) •
    ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)) _ w at hsecond
  rw [traceFreeHessian, hgradient.fderiv_eq, hsecond.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply]
  push_cast
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The Euclidean chart Laplacian of a radial scalar function. -/
@[category API, AMS 53]
private theorem chartLaplacian_comp_norm_sq (β : ℝ → ℝ) (w : ℂ)
    (hβ : ContDiffAt ℝ 2 β (‖w‖ ^ 2)) :
    chartLaplacian (fun z : ℂ ↦ β (‖z‖ ^ 2)) w =
      4 * (deriv β (‖w‖ ^ 2) + ‖w‖ ^ 2 *
        deriv (fun x ↦ deriv β x) (‖w‖ ^ 2)) := by
  have hs (z : ℂ) : HasFDerivAt (fun y : ℂ ↦ ‖y‖ ^ 2)
      ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) z := by
    have hre : HasFDerivAt (fun y : ℂ ↦ y.re) Complex.reCLM z :=
      Complex.reCLM.hasFDerivAt
    have him : HasFDerivAt (fun y : ℂ ↦ y.im) Complex.imCLM z :=
      Complex.imCLM.hasFDerivAt
    convert (hre.pow 2).add (him.pow 2) using 1
    · funext y
      simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm y
    · ext v
      simp
  have hβnear : ∀ᶠ z in nhds w, ContDiffAt ℝ 2 β (‖z‖ ^ 2) :=
    (contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun z : ℂ ↦ ‖z‖ ^ 2)).continuous.continuousAt.tendsto
      (hβ.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞))
  have hgradient : fderiv ℝ (fun z : ℂ ↦ β (‖z‖ ^ 2)) =ᶠ[nhds w] fun z ↦
      deriv β (‖z‖ ^ 2) •
        ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) := by
    filter_upwards [hβnear] with z hz
    have hcomp :=
      (hz.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp z (hs z)
    convert hcomp.fderiv using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hderivβ : ContDiffAt ℝ 1 (fun x ↦ deriv β x) (‖w‖ ^ 2) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      ((hβ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have hscalar : HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2))
      (deriv (fun x ↦ deriv β x) (‖w‖ ^ 2) •
        ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
    have hcomp :=
      (hderivβ.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp w (hs w)
    convert hcomp using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hre : HasFDerivAt (fun z : ℂ ↦ z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ ↦ z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hmatrix := ((hre.const_mul 2).smul_const Complex.reCLM).add
    ((him.const_mul 2).smul_const Complex.imCLM)
  have hsecond := hscalar.smul hmatrix
  change HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2) •
    ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)) _ w at hsecond
  rw [chartLaplacian, hgradient.fderiv_eq, hsecond.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

/-- Logarithmic derivative of the one-variable reciprocal damping factor. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalRadialDamping_deriv {s : ℝ} (hs : -10000 < s) :
    deriv (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) s =
        -(10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)) *
          (1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) := by
  have hden : s + 10000 ≠ 0 := by linarith
  have hfrac := (hasDerivAt_const s 10000).div
    ((hasDerivAt_id s).add_const 10000) hden
  have hψ := (counterexampleTwoReciprocalExponent_contDiff.differentiable (by simp) s).hasDerivAt
  have hraw := hfrac.mul hψ.neg.exp
  change deriv ((((fun _ : ℝ ↦ (10000 : ℝ)) / fun x ↦ id x + 10000) *
    fun x ↦ Real.exp ((-counterexampleTwoReciprocalExponent) x))) s = _
  rw [hraw.deriv]
  dsimp only [id_eq, Pi.div_apply, Pi.mul_apply, Pi.neg_apply]
  field_simp [hden]
  ring

/-- The scalar reciprocal damping factor is smooth wherever its rational denominator is
nonzero. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalRadialDamping_contDiffAt
    {s : ℝ} (hs : -10000 < s) {n : ℕ∞} :
    ContDiffAt ℝ n (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) s := by
  have hden : s + 10000 ≠ 0 := by linarith
  exact (contDiffAt_const.div (contDiffAt_id.add contDiffAt_const) hden).mul
    (counterexampleTwoReciprocalExponent_contDiff.contDiffAt.neg.exp.of_le (by simp))

/-- Second derivative of the one-variable reciprocal damping factor. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalRadialDamping_second_deriv
    {s : ℝ} (hs : -10000 < s) :
    deriv (fun y ↦ deriv (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) y) s =
        (10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)) *
          ((1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) ^ 2 +
            1 / (s + 10000) ^ 2 -
              deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s) := by
  let β : ℝ → ℝ := fun x ↦ 10000 / (x + 10000) *
    Real.exp (-counterexampleTwoReciprocalExponent x)
  have hden : s + 10000 ≠ 0 := by linarith
  have hfrac := (hasDerivAt_const s 10000).div
    ((hasDerivAt_id s).add_const 10000) hden
  have hψ := (counterexampleTwoReciprocalExponent_contDiff.differentiable (by simp) s).hasDerivAt
  have hβ := hfrac.mul hψ.neg.exp
  have hDψ : ContDiff ℝ ∞ (fun x ↦ deriv counterexampleTwoReciprocalExponent x) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      ((counterexampleTwoReciprocalExponent_contDiff.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (1 : ℝ))))
  have hψ₂ := (hDψ.differentiable (by simp) s).hasDerivAt
  have hq := (((hasDerivAt_id s).add_const 10000).inv hden).add hψ₂
  have hright := (hβ.mul hq).neg
  have hrightFun : (fun y ↦ -β y * (1 / (y + 10000) +
      deriv counterexampleTwoReciprocalExponent y)) =
      -((((fun _ : ℝ ↦ (10000 : ℝ)) / fun x ↦ id x + 10000) *
          fun x ↦ Real.exp ((-counterexampleTwoReciprocalExponent) x)) *
        ((fun x ↦ id x + 10000)⁻¹ +
          fun x ↦ deriv counterexampleTwoReciprocalExponent x)) := by
    funext y
    dsimp only [β, id_eq, Pi.div_apply, Pi.mul_apply, Pi.neg_apply, Pi.add_apply,
      Pi.inv_apply]
    ring
  have heq : (fun y ↦ deriv (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) y) =ᶠ[nhds s]
      fun y ↦ -β y * (1 / (y + 10000) + deriv counterexampleTwoReciprocalExponent y) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact counterexampleTwoReciprocalRadialDamping_deriv hy
  rw [heq.deriv_eq]
  rw [hrightFun, hright.deriv]
  simp only [id_eq, Pi.div_apply, Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.inv_apply]
  field_simp [hden]
  ring

/-- The stereographic trace-free Hessian of the reciprocal representative factors into its
positive damping coefficient and the explicit seed-plus-error model. -/
@[category API, AMS 53]
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal (w : ℂ) :
    let p := deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)
    let p' := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w =
      counterexampleTwoReciprocalDamping w *
        (traceFreeHessian counterexampleSeed w -
          8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
          4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w) := by
  let s := ‖w‖ ^ 2
  let β : ℝ → ℝ := fun x ↦ 10000 / (x + 10000) *
    Real.exp (-counterexampleTwoReciprocalExponent x)
  have hs0 : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hs : -10000 < s := by linarith
  have hβ : ContDiffAt ℝ 2 β s :=
    counterexampleTwoReciprocalRadialDamping_contDiffAt hs
  have hB : counterexampleTwoReciprocalDamping = fun z : ℂ ↦ β (‖z‖ ^ 2) := by
    rfl
  have hBbar : complexBarDeriv counterexampleTwoReciprocalDamping w =
      ((deriv β s : ℝ) : ℂ) * w := by
    rw [hB]
    exact complexBarDeriv_comp_norm_sq β w (hβ.differentiableAt (by norm_num))
  have hBtf : traceFreeHessian counterexampleTwoReciprocalDamping w =
      4 * ((deriv (fun x ↦ deriv β x) s : ℝ) : ℂ) * w ^ 2 := by
    rw [hB]
    exact traceFreeHessian_comp_norm_sq β w hβ
  have hβ' : deriv β s = -β s *
      (1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) :=
    counterexampleTwoReciprocalRadialDamping_deriv hs
  have hβ'' : deriv (fun x ↦ deriv β x) s = β s *
      ((1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) ^ 2 +
        1 / (s + 10000) ^ 2 -
          deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s) :=
    counterexampleTwoReciprocalRadialDamping_second_deriv hs
  have hprodSmooth : ContDiff ℝ ∞
      (fun z ↦ counterexampleTwoReciprocalDamping z * counterexampleSeed z) :=
    counterexampleTwoReciprocalDamping_contDiff.mul counterexampleSeed_contDiff
  have hprodDiff : Differentiable ℝ
      (fun z ↦ counterexampleTwoReciprocalDamping z * counterexampleSeed z) :=
    hprodSmooth.differentiable (by simp)
  change sphericalTraceFreeHessian 10000
      (fun z ↦ 10 ^ 10 + counterexampleTwoReciprocalDamping z * counterexampleSeed z) w = _
  rw [sphericalTraceFreeHessian,
    traceFreeHessian_const_add _ _ hprodSmooth,
    complexBarDeriv_const_add _ _ hprodDiff,
    traceFreeHessian_mul _ _ counterexampleTwoReciprocalDamping_contDiff
      counterexampleSeed_contDiff,
    complexBarDeriv_mul _ _
      (counterexampleTwoReciprocalDamping_contDiff.differentiable (by simp))
      (counterexampleSeed_contDiff.differentiable (by simp)),
    hBtf, hBbar, hβ', hβ'']
  rw [hB]
  dsimp only [s]
  simp only [div_eq_mul_inv, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_inv, one_mul, ← inv_pow]
  ring_nf

/-- In a conformal complex chart, a scalar shape operator forces the anti-linear coefficient
of the radius tensor to vanish. This is the algebraic core of the umbilic criterion. -/
@[category API, AMS 53]
private theorem antiLinearCoefficient_eq_zero_of_umbilic
    (dρ dF : ℂ →L[ℝ] ℝ³) (hdρ : Function.Injective dρ)
    (C r : ℝ) (A L Q : ℂ) (hr : r ≠ 0)
    (hformula : ∀ v : ℂ, dF v - C • dρ v =
      dρ (A * v + r • (L * v + Q * star v)))
    (humbilic : ∃ c : ℝ, dρ = c • dF) : Q = 0 := by
  obtain ⟨c, hc⟩ := humbilic
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    have hc' : dρ = 0 := hc.trans (zero_smul ℝ dF)
    exact one_ne_zero (hdρ (by rw [hc']; rfl))
  have hdF : dF = c⁻¹ • dρ := by
    rw [hc, inv_smul_smul₀ hc0]
  have hcoordinate (v : ℂ) :
      ((c⁻¹ - C : ℝ) : ℂ) * v = A * v + r • (L * v + Q * star v) := by
    apply hdρ
    rw [← hformula v, hdF]
    change dρ ((c⁻¹ - C) • v) = c⁻¹ • dρ v - C • dρ v
    rw [map_smul, sub_smul]
  have h1 := hcoordinate 1
  have hI := hcoordinate Complex.I
  have : (2 * r : ℂ) * Complex.I * Q = 0 := by
    have halgebra : (2 * r : ℂ) * Complex.I * Q =
        -((A * Complex.I + r • (L * Complex.I + Q * star Complex.I)) -
          Complex.I * (A * 1 + r • (L * 1 + Q * star (1 : ℂ)))) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [halgebra, ← hI, ← h1]
    ring
  exact (mul_eq_zero.mp this).resolve_left <|
    mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hr))
      Complex.I_ne_zero

/-- Norm estimate obtained from the conformal chart radius formula. -/
@[category API, AMS 53]
private theorem norm_radiusError_le_of_conformal_formula
    (dρ dF : ℂ →L[ℝ] ℝ³) (C k r : ℝ) (A L Q : ℂ)
    (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hscale : ∀ v : ℂ, ‖dρ v‖ = k * ‖v‖)
    (hformula : ∀ v : ℂ, dF v - C • dρ v =
      dρ (A * v + r • (L * v + Q * star v))) :
    ∀ v : ℂ, ‖dF v - C • dρ v‖ ≤
      (‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖dρ v‖ := by
  intro v
  rw [hformula, hscale]
  calc
    k * ‖A * v + r • (L * v + Q * star v)‖ ≤
        k * ((‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖v‖) := by
      gcongr
      calc
        ‖A * v + r • (L * v + Q * star v)‖ ≤
            ‖A * v‖ + ‖r • (L * v + Q * star v)‖ := norm_add_le _ _
        _ = ‖A‖ * ‖v‖ + |r| * ‖L * v + Q * star v‖ := by
          rw [norm_mul, norm_smul, Real.norm_eq_abs]
        _ ≤ ‖A‖ * ‖v‖ + r * (‖L * v‖ + ‖Q * star v‖) := by
          rw [abs_of_nonneg hr]
          gcongr
          exact norm_add_le _ _
        _ = (‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖v‖ := by
          rw [norm_mul, norm_mul, norm_star]
          ring
    _ = (‖A‖ + r * (‖L‖ + ‖Q‖)) * (k * ‖v‖) := by ring
    _ = (‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖dρ v‖ := by rw [hscale]

/-- The seed's trace-free Hessian cannot be cancelled by error terms having the two bounds
which arise from differentiating the reciprocal damping factor. -/
@[category API, AMS 53]
private theorem seedTraceFreeHessian_perturbation_ne_zero (w : ℂ) (p p' : ℝ)
    (hp : ‖w‖ * |p| ≤ 1 / 100)
    (hpp : ‖w‖ ^ 2 * (p ^ 2 + |p'|) ≤ 1 / 1000) :
    traceFreeHessian counterexampleSeed w -
        8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
      4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w ≠ 0 := by
  have hbar : ‖complexBarDeriv counterexampleSeed w‖ ≤ 129 / 80 := by
    have hnorm : ‖complexBarDeriv counterexampleSeed w‖ =
        ‖((fderiv ℝ counterexampleSeed w 1 : ℂ) -
          (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2‖ := by
      rw [complexBarDeriv, show
        ((fderiv ℝ counterexampleSeed w 1 : ℂ) +
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2 =
          star (((fderiv ℝ counterexampleSeed w 1 : ℂ) -
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2) by
          simp,
        norm_star]
    rw [hnorm]
    exact counterexampleSeed_wirtinger_norm_upper w
  have hseed : |counterexampleSeed w| ≤ 253 / 160 := counterexampleSeed_abs_le w
  have hpabs : |p ^ 2 - p'| ≤ p ^ 2 + |p'| := by
    calc
      |p ^ 2 - p'| ≤ |p ^ 2| + |p'| := abs_sub _ _
      _ = p ^ 2 + |p'| := by rw [abs_of_nonneg (sq_nonneg p)]
  have hpperr : ‖w‖ ^ 2 * |p ^ 2 - p'| ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpabs (sq_nonneg ‖w‖)).trans hpp
  have hfirst : ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ ≤
      129 / 1000 := by
    calc
      ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ =
          8 * (‖w‖ * |p|) * ‖complexBarDeriv counterexampleSeed w‖ := by
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ 8 * (1 / 100) * (129 / 80) := by gcongr
      _ = 129 / 1000 := by norm_num
  have hsecond :
      ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        253 / 40000 := by
    calc
      ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ =
          4 * (‖w‖ ^ 2 * |p ^ 2 - p'|) * |counterexampleSeed w| := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs]
        ring
      _ ≤ 4 * (1 / 1000) * (253 / 160) := by gcongr
      _ = 253 / 40000 := by norm_num
  have herror :
      ‖-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w) +
          4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        5413 / 40000 := by
    calc
      _ ≤ ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ +
          ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ := by
        simpa only [norm_neg] using norm_add_le
          (-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w))
          (4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w)
      _ ≤ 129 / 1000 + 253 / 40000 := add_le_add hfirst hsecond
      _ = 5413 / 40000 := by norm_num
  intro hzero
  have hsum : traceFreeHessian counterexampleSeed w +
      (-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w) +
        4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w) = 0 := by
    simpa only [sub_eq_add_neg, add_assoc] using hzero
  have hnormeq : ‖traceFreeHessian counterexampleSeed w‖ =
      ‖-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w) +
        4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ := by
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
  have hlower := counterexampleSeed_traceFreeHessian_norm_lower w
  rw [hnormeq] at hlower
  linarith

/-- A deliberately loose upper bound for the same reciprocal trace-free model. -/
@[category API, AMS 53]
private theorem seedTraceFreeHessian_perturbation_norm_upper (w : ℂ) (p p' : ℝ)
    (hp : ‖w‖ * |p| ≤ 1 / 100)
    (hpp : ‖w‖ ^ 2 * (p ^ 2 + |p'|) ≤ 1 / 1000) :
    ‖traceFreeHessian counterexampleSeed w -
        8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
      4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤ 20 := by
  have hbar : ‖complexBarDeriv counterexampleSeed w‖ ≤ 129 / 80 := by
    have hnorm : ‖complexBarDeriv counterexampleSeed w‖ =
        ‖((fderiv ℝ counterexampleSeed w 1 : ℂ) -
          (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2‖ := by
      rw [complexBarDeriv, show
        ((fderiv ℝ counterexampleSeed w 1 : ℂ) +
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2 =
          star (((fderiv ℝ counterexampleSeed w 1 : ℂ) -
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2) by
          simp,
        norm_star]
    rw [hnorm]
    exact counterexampleSeed_wirtinger_norm_upper w
  have hpabs : |p ^ 2 - p'| ≤ p ^ 2 + |p'| := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg p)])
  have hpperr : ‖w‖ ^ 2 * |p ^ 2 - p'| ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpabs (sq_nonneg ‖w‖)).trans hpp
  have hfirst : ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ ≤
      129 / 1000 := by
    calc
      _ = 8 * (‖w‖ * |p|) * ‖complexBarDeriv counterexampleSeed w‖ := by
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ 8 * (1 / 100) * (129 / 80) := by gcongr
      _ = 129 / 1000 := by norm_num
  have hsecond :
      ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        253 / 40000 := by
    calc
      _ = 4 * (‖w‖ ^ 2 * |p ^ 2 - p'|) * |counterexampleSeed w| := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs]
        ring
      _ ≤ 4 * (1 / 1000) * (253 / 160) := by
        gcongr
        exact counterexampleSeed_abs_le w
      _ = 253 / 40000 := by norm_num
  calc
    _ ≤ ‖traceFreeHessian counterexampleSeed w‖ +
        ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ +
        ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ := by
      calc
        _ ≤ ‖traceFreeHessian counterexampleSeed w -
              8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ +
            ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ :=
          norm_add_le _ _
        _ ≤ (‖traceFreeHessian counterexampleSeed w‖ +
              ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖) +
            ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ 47 / 10 + 129 / 1000 + 253 / 40000 :=
      add_le_add (add_le_add (counterexampleSeed_traceFreeHessian_norm_upper w) hfirst) hsecond
    _ ≤ 20 := by norm_num

/-- The first derivative of the reciprocal exponent on the positive half-line. The formula is
kept in the original radial variable so later estimates may choose their own rescaling. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_deriv_of_pos {s : ℝ} (hs : 0 < s) :
    deriv counterexampleTwoReciprocalExponent s =
      ((1 / 8 : ℝ) * (s / 10000) ^ (-(7 : ℝ) / 8) / 10000) *
          Real.exp (-10000 / s) +
        (s / 10000) ^ ((1 : ℝ) / 8) * Real.exp (-10000 / s) *
          (10000 / s ^ 2) := by
  have heq : counterexampleTwoReciprocalExponent =ᶠ[nhds s]
      fun x : ℝ ↦ (x / 10000) ^ ((1 : ℝ) / 8) * Real.exp (-10000 / x) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact counterexampleTwoReciprocalExponent_of_pos hx
  have hpow := ((hasDerivAt_id s).div_const 10000).rpow_const (p := (1 / 8 : ℝ))
    (Or.inl (div_ne_zero hs.ne' (by norm_num)))
  have hexp := ((hasDerivAt_const s (-10000)).div (hasDerivAt_id s) hs.ne').exp
  have hprod := hpow.mul hexp
  rw [heq.deriv_eq]
  change deriv ((fun x : ℝ ↦ (x / 10000) ^ ((1 : ℝ) / 8) *
    Real.exp (-10000 / x))) s = _
  rw [show deriv ((fun x : ℝ ↦ (x / 10000) ^ ((1 : ℝ) / 8) *
      Real.exp (-10000 / x))) s = _ by
    simpa only [id_eq, Pi.div_apply] using hprod.deriv]
  ring

/-- The same first derivative in the dimensionless variable `t = 10000 / s`. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_deriv_dimensionless {s : ℝ} (hs : 0 < s) :
    let t := 10000 / s
    deriv counterexampleTwoReciprocalExponent s =
      1 / 10000 * Real.exp (-t) *
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) := by
  let t := 10000 / s
  change deriv counterexampleTwoReciprocalExponent s =
    1 / 10000 * Real.exp (-t) *
      ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ))
  have ht : 0 < t := div_pos (by norm_num) hs
  have ht_inv : t = (s / 10000)⁻¹ := by
    dsimp [t]
    field_simp
  have hrpow (a : ℝ) : (s / 10000) ^ a = t ^ (-a) := by
    rw [ht_inv, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hs_over : 10000 / s ^ 2 = t ^ 2 / 10000 := by
    dsimp [t]
    field_simp
  rw [counterexampleTwoReciprocalExponent_deriv_of_pos hs, hrpow, hrpow, hs_over]
  have hexp : -10000 / s = -t := by
    dsimp only [t]
    ring
  rw [hexp]
  norm_num only [neg_div, neg_neg]
  have hshift : t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ) = t ^ (15 / 8 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  rw [← Real.rpow_two t]
  rw [show (-(1 / 8 : ℝ)) = (-(1 : ℝ) / 8) by ring]
  calc
    ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) / 10000 * Real.exp (-t) +
        t ^ (-(1 : ℝ) / 8) * Real.exp (-t) * (t ^ (2 : ℝ) / 10000)) =
        1 / 10000 * Real.exp (-t) *
          ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) +
            t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ)) := by ring
    _ = _ := by rw [hshift]

/-- The second reciprocal-exponent derivative in the same dimensionless variable. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_second_deriv_dimensionless
    {s : ℝ} (hs : 0 < s) :
    let t := 10000 / s
    deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s =
      -(1 / 100000000 : ℝ) * Real.exp (-t) *
        ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)) := by
  let t := 10000 / s
  change deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s =
    -(1 / 100000000 : ℝ) * Real.exp (-t) *
      ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
        (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ))
  have ht : 0 < t := div_pos (by norm_num) hs
  let P : ℝ → ℝ := fun x ↦
    let y := 10000 / x
    1 / 10000 * Real.exp (-y) *
      ((1 / 8 : ℝ) * y ^ (7 / 8 : ℝ) + y ^ (15 / 8 : ℝ))
  have heq : (fun x ↦ deriv counterexampleTwoReciprocalExponent x) =ᶠ[nhds s] P := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact counterexampleTwoReciprocalExponent_deriv_dimensionless hx
  have hT₀ : HasDerivAt (fun x : ℝ ↦ 10000 / x) (-10000 / s ^ 2) s := by
    convert (hasDerivAt_const s 10000).div (hasDerivAt_id s) hs.ne' using 1
    all_goals
      simp only [id_eq]
      field_simp [hs.ne']
      ring
  have hcoef : -10000 / s ^ 2 = -t ^ 2 / 10000 := by
    dsimp only [t]
    field_simp [hs.ne']
  have hT : HasDerivAt (fun x : ℝ ↦ 10000 / x) (-t ^ 2 / 10000) s := by
    simpa only [hcoef] using hT₀
  have hA := ((hT.rpow_const (p := (7 / 8 : ℝ)) (Or.inl ht.ne')).const_mul
    (1 / 8 : ℝ)).add
      (hT.rpow_const (p := (15 / 8 : ℝ)) (Or.inl ht.ne'))
  have hP := (hasDerivAt_const s (1 / 10000 : ℝ)).mul (hT.neg.exp.mul hA)
  calc
    deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s = deriv P s :=
      heq.deriv_eq
    _ = _ := by
      rw [show deriv P s = _ by
        simpa only [P, Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply, id_eq,
          mul_assoc] using hP.deriv]
      rw [show 10000 / s = t by rfl]
      rw [← Real.rpow_two t]
      ring_nf
      have h23 : t ^ (7 / 8 : ℝ) * t ^ (2 : ℝ) = t ^ (23 / 8 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        norm_num
      have h31 : t ^ (15 / 8 : ℝ) * t ^ (2 : ℝ) = t ^ (31 / 8 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        norm_num
      have h15 : t ^ (2 : ℝ) * t ^ (-(1 : ℝ) / 8) = t ^ (15 / 8 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        norm_num
      have hterm23 : Real.exp (-t) * t ^ (7 / 8 : ℝ) * t ^ (2 : ℝ) =
          Real.exp (-t) * t ^ (23 / 8 : ℝ) := by rw [mul_assoc, h23]
      have hterm31 : Real.exp (-t) * t ^ (15 / 8 : ℝ) * t ^ (2 : ℝ) =
          Real.exp (-t) * t ^ (31 / 8 : ℝ) := by rw [mul_assoc, h31]
      have hterm15 : Real.exp (-t) * t ^ (2 : ℝ) * t ^ (-(1 : ℝ) / 8) =
          Real.exp (-t) * t ^ (15 / 8 : ℝ) := by rw [mul_assoc, h15]
      rw [hterm23, hterm31, hterm15]
      ring

/-- After the substitution `t = 10000 / ‖w‖²`, the first reciprocal-exponent derivative is
exactly the numerator controlled by `reciprocalDampingFirstNumerator_bound`. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_deriv_rescaled {w : ℂ} (hw : w ≠ 0) :
    let t := 10000 / ‖w‖ ^ 2
    ‖w‖ * |deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)| =
      1 / 100 * (Real.exp (-t) *
        ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ))) := by
  let r := ‖w‖
  let s := r ^ 2
  let t := 10000 / s
  change r * |deriv counterexampleTwoReciprocalExponent s| =
    1 / 100 * (Real.exp (-t) *
      ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ)))
  have hr : 0 < r := norm_pos_iff.mpr hw
  have hs : 0 < s := sq_pos_of_pos hr
  have ht : 0 < t := div_pos (by norm_num) hs
  have ht_inv : t = (s / 10000)⁻¹ := by
    dsimp [t]
    field_simp
  have hrpow (a : ℝ) : (s / 10000) ^ a = t ^ (-a) := by
    rw [ht_inv, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hs_over : 10000 / s ^ 2 = t ^ 2 / 10000 := by
    dsimp [t]
    field_simp
  have hr_eq : r = 100 * t ^ (-(1 : ℝ) / 2) := by
    have hsquare : r ^ 2 = (100 * t ^ (-(1 : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, ← Real.rpow_mul_natCast ht.le (-(1 : ℝ) / 2) 2,
        show (-(1 : ℝ) / 2) * (2 : ℕ) = -(1 : ℝ) by norm_num,
        Real.rpow_neg ht.le, Real.rpow_one]
      dsimp [t, s]
      field_simp
      norm_num
    obtain h | h := eq_or_eq_neg_of_sq_eq_sq r
      (100 * t ^ (-(1 : ℝ) / 2)) hsquare
    · exact h
    · nlinarith [hr, Real.rpow_pos_of_pos ht (-(1 : ℝ) / 2)]
  rw [counterexampleTwoReciprocalExponent_deriv_of_pos hs, abs_of_nonneg (by positivity),
    hrpow, hrpow, hs_over, hr_eq]
  have hexp : -10000 / s = -t := by
    dsimp only [t]
    ring
  rw [hexp]
  norm_num only [neg_div, neg_neg]
  have hshift₁ : t ^ (-(1 : ℝ) / 2) * t ^ (7 / 8 : ℝ) = t ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  have hshift₂ : t ^ (-(1 : ℝ) / 2) *
      (t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ)) = t ^ (11 / 8 : ℝ) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    norm_num
  rw [← Real.rpow_two t]
  rw [show (-(1 / 2 : ℝ)) = (-(1 : ℝ) / 2) by ring,
    show (-(1 / 8 : ℝ)) = (-(1 : ℝ) / 8) by ring]
  calc
    100 * t ^ (-(1 : ℝ) / 2) *
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) / 10000 * Real.exp (-t) +
          t ^ (-(1 : ℝ) / 8) * Real.exp (-t) * (t ^ (2 : ℝ) / 10000)) =
        1 / 100 * Real.exp (-t) *
          ((1 / 8 : ℝ) * (t ^ (-(1 : ℝ) / 2) * t ^ (7 / 8 : ℝ)) +
            t ^ (-(1 : ℝ) / 2) *
              (t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ))) := by ring
    _ = _ := by
      rw [hshift₁, hshift₂]
      ring

/-- Uniform first-derivative bound for the reciprocal exponent away from the reciprocal-chart
origin. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_first_bound {w : ℂ} (hw : w ≠ 0) :
    ‖w‖ * |deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)| ≤ 1 / 100 := by
  rw [counterexampleTwoReciprocalExponent_deriv_rescaled hw]
  have ht : 0 ≤ 10000 / ‖w‖ ^ 2 := by positivity
  have h := reciprocalDampingFirstNumerator_bound ht
  nlinarith

/-- Uniform combined first/second derivative bound for the reciprocal exponent. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_second_bound {w : ℂ} (hw : w ≠ 0) :
    ‖w‖ ^ 2 * (deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2) ^ 2 +
      |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)|) ≤
        1 / 1000 := by
  let s := ‖w‖ ^ 2
  let t := 10000 / s
  change s * (deriv counterexampleTwoReciprocalExponent s ^ 2 +
    |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s|) ≤ 1 / 1000
  have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have ht : 0 < t := div_pos (by norm_num) hs
  have hs_eq : s = 10000 / t := by
    dsimp [t]
    field_simp
  have hp := counterexampleTwoReciprocalExponent_deriv_dimensionless hs
  have hpp := counterexampleTwoReciprocalExponent_second_deriv_dimensionless hs
  have hp' : deriv counterexampleTwoReciprocalExponent s =
      1 / 10000 * Real.exp (-t) *
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) := hp
  have hpp' : deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s =
      -(1 / 100000000 : ℝ) * Real.exp (-t) *
        ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)) := hpp
  have hbracket :
      |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)| ≤
        (7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ) := by
    calc
      |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)| ≤
          |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ)| + |t ^ (31 / 8 : ℝ)| := abs_sub _ _
      _ ≤ |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ)| +
          |(7 / 4 : ℝ) * t ^ (23 / 8 : ℝ)| + |t ^ (31 / 8 : ℝ)| := by
        gcongr
        exact abs_add_le _ _
      _ = (7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ) := by
        rw [abs_of_nonneg, abs_of_nonneg, abs_of_nonneg]
        all_goals positivity
  have hp_part : s * deriv counterexampleTwoReciprocalExponent s ^ 2 =
      1 / 10000 * (Real.exp (-2 * t) *
        ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
          (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ))) := by
    rw [hp', hs_eq]
    have h77 : t ^ (7 / 8 : ℝ) * t ^ (7 / 8 : ℝ) = t ^ (7 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h715 : t ^ (7 / 8 : ℝ) * t ^ (15 / 8 : ℝ) = t ^ (11 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h1515 : t ^ (15 / 8 : ℝ) * t ^ (15 / 8 : ℝ) = t ^ (15 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h13 : t * t ^ (3 / 4 : ℝ) = t ^ (7 / 4 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h17 : t * t ^ (7 / 4 : ℝ) = t ^ (11 / 4 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h111 : t * t ^ (11 / 4 : ℝ) = t ^ (15 / 4 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have hc13 : t * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ)) =
        (1 / 64 : ℝ) * t ^ (7 / 4 : ℝ) := by
      calc
        t * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ)) =
            (1 / 64 : ℝ) * (t * t ^ (3 / 4 : ℝ)) := by ring
        _ = _ := by rw [h13]
    have hc17 : t * ((1 / 4 : ℝ) * t ^ (7 / 4 : ℝ)) =
        (1 / 4 : ℝ) * t ^ (11 / 4 : ℝ) := by
      calc
        t * ((1 / 4 : ℝ) * t ^ (7 / 4 : ℝ)) =
            (1 / 4 : ℝ) * (t * t ^ (7 / 4 : ℝ)) := by ring
        _ = _ := by rw [h17]
    have hsq :
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) ^ 2 =
          t * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
            (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) := by
      calc
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) ^ 2 =
            (1 / 64 : ℝ) * (t ^ (7 / 8 : ℝ) * t ^ (7 / 8 : ℝ)) +
              (1 / 4 : ℝ) * (t ^ (7 / 8 : ℝ) * t ^ (15 / 8 : ℝ)) +
              t ^ (15 / 8 : ℝ) * t ^ (15 / 8 : ℝ) := by ring
        _ = (1 / 64 : ℝ) * t ^ (7 / 4 : ℝ) +
              (1 / 4 : ℝ) * t ^ (11 / 4 : ℝ) + t ^ (15 / 4 : ℝ) := by
          rw [h77, h715, h1515]
        _ = _ := by rw [mul_add, mul_add, hc13, hc17, h111]
    have hexpSq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      10000 / t *
          (1 / 10000 * Real.exp (-t) *
            ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ))) ^ 2 =
          10000 / t * ((1 / 10000 : ℝ) ^ 2 * Real.exp (-t) ^ 2 *
            ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) ^ 2) := by
            ring
      _ = _ := by
        rw [hexpSq, hsq]
        field_simp [ht.ne']
  have hpp_part : s *
      |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s| ≤
      1 / 10000 * (Real.exp (-t) *
        ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ))) := by
    rw [hpp']
    rw [abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100000000),
      abs_of_nonneg (Real.exp_nonneg _)]
    calc
      s * (1 / 100000000 * Real.exp (-t) *
          |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)|) ≤
          s * (1 / 100000000 * Real.exp (-t) *
            ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
              (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ))) := by
        gcongr
      _ = 1 / 10000 * (Real.exp (-t) *
          ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ))) := by
        rw [hs_eq]
        have h7 : t * t ^ (7 / 8 : ℝ) = t ^ (15 / 8 : ℝ) := by
          nth_rewrite 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
        have h15 : t * t ^ (15 / 8 : ℝ) = t ^ (23 / 8 : ℝ) := by
          nth_rewrite 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
        have h23 : t * t ^ (23 / 8 : ℝ) = t ^ (31 / 8 : ℝ) := by
          nth_rewrite 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
        have hshift :
            (7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
                (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ) =
              t * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
                (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ)) := by
          calc
            _ = (7 / 64 : ℝ) * (t * t ^ (7 / 8 : ℝ)) +
                (7 / 4 : ℝ) * (t * t ^ (15 / 8 : ℝ)) +
                t * t ^ (23 / 8 : ℝ) := by rw [h7, h15, h23]
            _ = _ := by ring
        rw [hshift]
        field_simp [ht.ne']
        ring
  rw [mul_add, hp_part]
  calc
    1 / 10000 * (Real.exp (-2 * t) *
        ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
          (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ))) +
      s * |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s| ≤
        1 / 10000 * (Real.exp (-2 * t) *
          ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
            (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) +
          Real.exp (-t) * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ))) := by
          nlinarith
    _ ≤ 1 / 10000 * 10 := by
      gcongr
      exact (reciprocalDampingSecondNumerator_bound ht.le).le
    _ = 1 / 1000 := by norm_num

/-- A direct, deliberately loose bound for the first radial derivative. Unlike the rescaled
bound above, this remains useful in the Laplacian formula at the reciprocal origin. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalExponent_deriv_abs_le (s : ℝ) (hs : 0 ≤ s) :
    |deriv counterexampleTwoReciprocalExponent s| ≤ 1 / 1000 := by
  by_cases hs0 : s = 0
  · subst s
    let f : ℝ → ℝ := fun x ↦ x ^ ((1 : ℝ) / 8) * Real.flatRpowExp 1 10000 x
    have hflat := Real.flatRpowExp.rpow_mul_iteratedFDeriv_zero
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 10000) ((1 : ℝ) / 8) 1
    have hfderiv : fderiv ℝ f 0 = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      have happ := congrArg (fun L : ℝ [×1]→L[ℝ] ℝ ↦ L ![v]) hflat
      simpa only [f, iteratedFDeriv_one_apply,
        ContinuousMultilinearMap.zero_apply] using happ
    have hfcont : ContDiff ℝ ∞ f :=
      Real.flatRpowExp.rpow_mul_contDiff (by norm_num) (by norm_num) ((1 : ℝ) / 8)
    have hfDiff : DifferentiableAt ℝ f 0 := hfcont.differentiable (by simp) 0
    have hderiv : deriv f 0 = 0 := by rw [deriv, hfderiv]; rfl
    change |deriv (fun x : ℝ ↦ (10000 : ℝ) ^ (-(1 : ℝ) / 8) * f x) 0| ≤ 1 / 1000
    rw [deriv_const_mul _ hfDiff, hderiv, mul_zero, abs_zero]
    norm_num
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let t := 10000 / s
    have ht : 0 < t := div_pos (by norm_num) hspos
    rw [counterexampleTwoReciprocalExponent_deriv_dimensionless hspos,
      abs_of_nonneg (by positivity)]
    have h₁ : t ^ (7 / 8 : ℝ) * Real.exp (-t) ≤ 1 :=
      rpow_mul_exp_neg_le_one (a := 7 / 8) ht.le (by norm_num) (by norm_num)
    have h₂ : t ^ (15 / 8 : ℝ) * Real.exp (-t) ≤ 15 / 16 :=
      (rpow_mul_exp_neg_le_self (a := 15 / 8) ht.le (by norm_num)).trans
        ((self_rpow_mul_exp_neg_le_half (a := 15 / 8) (by norm_num) (by norm_num)).trans_eq
          (by norm_num))
    calc
      1 / 10000 * Real.exp (-t) *
          ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) =
        1 / 10000 * ((1 / 8 : ℝ) *
          (t ^ (7 / 8 : ℝ) * Real.exp (-t)) +
            t ^ (15 / 8 : ℝ) * Real.exp (-t)) := by ring
      _ ≤ 1 / 10000 * ((1 / 8 : ℝ) * 1 + 15 / 16) := by gcongr
      _ ≤ 1 / 1000 := by norm_num

/-- The conjugate Wirtinger convention used by the support calculation has the same seed bound
as the convention used in the planar index calculation. -/
@[category API, AMS 53]
private theorem complexBarDeriv_counterexampleSeed_norm_upper (w : ℂ) :
    ‖complexBarDeriv counterexampleSeed w‖ ≤ 129 / 80 := by
  have hconj :
      star (((fderiv ℝ counterexampleSeed w 1 : ℂ) -
          (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2) =
        complexBarDeriv counterexampleSeed w := by
    rw [complexBarDeriv]
    simp
  rw [← hconj, norm_star]
  exact counterexampleSeed_wirtinger_norm_upper w

/-- The Euclidean chart Laplacian of the reciprocal representative is controlled by eight
times its positive damping factor. The argument deliberately keeps substantial numerical
slack, since only positivity of the resulting radius tensor matters. -/
@[category API, AMS 53]
private theorem chartLaplacian_counterexampleTwoReciprocal_le_of_seed
    (hSeedLaplacian : ∀ z : ℂ, |chartLaplacian counterexampleSeed z| ≤ 47 / 10)
    (w : ℂ) :
    |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w := by
  let s : ℝ := ‖w‖ ^ 2
  let D : ℝ := s + 10000
  let p : ℝ := deriv counterexampleTwoReciprocalExponent s
  let p' : ℝ := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s
  let q : ℝ := 1 / D + p
  let β : ℝ → ℝ := fun x ↦ 10000 / (x + 10000) *
    Real.exp (-counterexampleTwoReciprocalExponent x)
  let B : ℂ → ℝ := counterexampleTwoReciprocalDamping
  have hs : 0 ≤ s := sq_nonneg _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hBpos : 0 < B w := by
    dsimp only [B, counterexampleTwoReciprocalDamping]
    positivity
  have hβ : ContDiffAt ℝ 2 β s := by
    exact counterexampleTwoReciprocalRadialDamping_contDiffAt (by linarith [hs])
  have hβ₁ : deriv β s = -(B w) * q := by
    rw [counterexampleTwoReciprocalRadialDamping_deriv (by linarith [hs])]
    rfl
  have hβ₂ : deriv (fun x ↦ deriv β x) s =
      B w * (q ^ 2 + 1 / D ^ 2 - p') := by
    rw [counterexampleTwoReciprocalRadialDamping_second_deriv
      (by linarith [hs])]
    rfl
  have hp : |p| ≤ 1 / 1000 :=
    counterexampleTwoReciprocalExponent_deriv_abs_le s hs
  have hrp : ‖w‖ * |p| ≤ 1 / 100 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact counterexampleTwoReciprocalExponent_first_bound hw
  have hpp : s * (p ^ 2 + |p'|) ≤ 1 / 1000 := by
    by_cases hw : w = 0
    · simp [hw, s]
    · simpa only [s, p, p'] using counterexampleTwoReciprocalExponent_second_bound hw
  have hrD : ‖w‖ / D ≤ 1 / 200 := by
    have hsquare := sq_nonneg (‖w‖ - 100)
    dsimp only [D, s]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hsD : s / D ^ 2 ≤ 1 / 10000 := by
    dsimp only [D]
    apply (div_le_iff₀ (sq_pos_of_pos hD)).2
    nlinarith [sq_nonneg s]
  have hq : |q| ≤ 11 / 10000 := by
    calc
      |q| ≤ |1 / D| + |p| := by dsimp only [q]; exact abs_add_le ..
      _ = 1 / D + |p| := by rw [abs_of_pos (one_div_pos.mpr hD)]
      _ ≤ 1 / 10000 + 1 / 1000 := by
        gcongr
        change 10000 ≤ D
        dsimp only [D]
        linarith [hs]
      _ = 11 / 10000 := by norm_num
  have hrq : ‖w‖ * |q| ≤ 3 / 200 := by
    calc
      ‖w‖ * |q| ≤ ‖w‖ * (|1 / D| + |p|) := by
        gcongr
        dsimp only [q]
        exact abs_add_le ..
      _ = ‖w‖ / D + ‖w‖ * |p| := by
        rw [abs_of_pos (one_div_pos.mpr hD)]
        ring
      _ ≤ 1 / 200 + 1 / 100 := add_le_add hrD hrp
      _ = 3 / 200 := by norm_num
  have hinside :
      |-(q) + s * (q ^ 2 + 1 / D ^ 2 - p')| ≤ 1 / 40 := by
    calc
      |-(q) + s * (q ^ 2 + 1 / D ^ 2 - p')| ≤
          |q| + s * (q ^ 2 + 1 / D ^ 2 + |p'|) := by
        calc
          _ ≤ |-q| + |s * (q ^ 2 + 1 / D ^ 2 - p')| := abs_add_le ..
          _ = |q| + s * |q ^ 2 + 1 / D ^ 2 - p'| := by
            rw [abs_neg, abs_mul, abs_of_nonneg hs]
          _ ≤ |q| + s * (q ^ 2 + 1 / D ^ 2 + |p'|) := by
            gcongr
            calc
              |q ^ 2 + 1 / D ^ 2 - p'| ≤
                  |q ^ 2 + 1 / D ^ 2| + |p'| := abs_sub ..
              _ = q ^ 2 + 1 / D ^ 2 + |p'| := by
                rw [abs_of_nonneg]
                positivity
      _ ≤ 11 / 10000 +
          s * (2 * (1 / D ^ 2 + p ^ 2) + 1 / D ^ 2 + |p'|) := by
        gcongr
        dsimp only [q]
        have hdivsq : (1 / D) ^ 2 = 1 / D ^ 2 := by ring
        rw [← hdivsq]
        nlinarith [sq_nonneg (1 / D - p)]
      _ ≤ 11 / 10000 + 3 * (1 / 10000) + 2 * (1 / 1000) := by
        have hrewrite : s * (2 * (1 / D ^ 2 + p ^ 2) + 1 / D ^ 2 + |p'|) =
            3 * (s / D ^ 2) + 2 * (s * (p ^ 2 + |p'|)) - s * |p'| := by
          ring
        rw [hrewrite]
        nlinarith [hsD, hpp, mul_nonneg hs (abs_nonneg p')]
      _ ≤ 1 / 40 := by norm_num
  have hLaplacianB : |chartLaplacian B w| ≤ B w / 10 := by
    have hBrep : B = fun z : ℂ ↦ β (‖z‖ ^ 2) := by rfl
    rw [hBrep, chartLaplacian_comp_norm_sq β w hβ, hβ₁, hβ₂]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    change 4 * |-B w * q + ‖w‖ ^ 2 * (B w * (q ^ 2 + 1 / D ^ 2 - p'))| ≤
      β (‖w‖ ^ 2) / 10
    change 4 * |-B w * q + s * (B w * (q ^ 2 + 1 / D ^ 2 - p'))| ≤ β s / 10
    rw [show β s = B w by rfl]
    rw [show -B w * q + s * (B w * (q ^ 2 + 1 / D ^ 2 - p')) =
      B w * (-q + s * (q ^ 2 + 1 / D ^ 2 - p')) by ring,
      abs_mul, abs_of_pos hBpos]
    calc
      4 * (B w * |-(q) + s * (q ^ 2 + 1 / D ^ 2 - p')|) ≤
          4 * (B w * (1 / 40)) := by gcongr
      _ = B w / 10 := by ring
  have hDB (v : ℂ) : fderiv ℝ B w v =
      -2 * B w * q * inner ℝ w v := by
    have hβderiv : HasDerivAt β (-(B w) * q) s := by
      convert (hβ.differentiableAt (by norm_num)).hasDerivAt using 1
      exact hβ₁.symm
    have hsderiv : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2) (2 • innerSL ℝ w) w := by
      simpa only [two_smul] using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
    have hcomp := hβderiv.hasFDerivAt.comp w hsderiv
    have hBrep : B = fun z : ℂ ↦ β (‖z‖ ^ 2) := by rfl
    rw [hBrep]
    change fderiv ℝ (β ∘ fun z : ℂ ↦ ‖z‖ ^ 2) w v =
      -2 * β s * q * inner ℝ w v
    rw [hcomp.fderiv]
    simp
    rw [show β s = B w by rfl]
    ring
  have hcross :
      |2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
        fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I)| ≤
          B w / 2 := by
    let g := complexBarDeriv counterexampleSeed w
    have hg : ‖g‖ ≤ 129 / 80 := complexBarDeriv_counterexampleSeed_norm_upper w
    have hidentity :
        2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
          fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I) =
            -8 * B w * q * (w * star g).re := by
      rw [hDB, hDB]
      dsimp only [g, complexBarDeriv]
      simp [Complex.inner, Complex.mul_re, Complex.mul_im]
      ring
    rw [hidentity, abs_mul, abs_mul, abs_mul, abs_of_pos hBpos]
    have hre : |(w * star g).re| ≤ ‖w‖ * ‖g‖ := by
      calc
        |(w * star g).re| ≤ ‖w * star g‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖g‖ := by rw [norm_mul, norm_star]
    calc
      |(-8 : ℝ)| * B w * |q| * |(w * star g).re| ≤
        8 * B w * |q| * (‖w‖ * ‖g‖) := by
          norm_num
          exact mul_le_mul_of_nonneg_left
            (show |w.re * g.re + w.im * g.im| ≤ ‖w‖ * ‖g‖ by
              simpa [Complex.mul_re] using hre)
            (mul_nonneg (mul_nonneg (by norm_num) hBpos.le) (abs_nonneg q))
      _ = B w * (8 * (‖w‖ * |q|) * ‖g‖) := by ring
      _ ≤ B w * (8 * (3 / 200) * (129 / 80)) := by
        gcongr
      _ ≤ B w / 2 := by nlinarith [hBpos]
  have hproduct := chartLaplacian_mul B counterexampleSeed
    counterexampleTwoReciprocalDamping_contDiff counterexampleSeed_contDiff w
  have hsum : |chartLaplacian (fun z ↦ B z * counterexampleSeed z) w| ≤
      B w * (47 / 10) + (253 / 160) * (B w / 10) + B w / 2 := by
    rw [hproduct]
    calc
      |B w * chartLaplacian counterexampleSeed w +
          counterexampleSeed w * chartLaplacian B w +
            2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
              fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I)| ≤
          |B w * chartLaplacian counterexampleSeed w| +
            |counterexampleSeed w * chartLaplacian B w| +
              |2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
                fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I)| := by
        exact (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
      _ ≤ B w * (47 / 10) + (253 / 160) * (B w / 10) + B w / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos hBpos]
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left (hSeedLaplacian w) hBpos.le)
            (mul_le_mul (counterexampleSeed_abs_le w) hLaplacianB
              (abs_nonneg _) (by positivity))) hcross
  change |chartLaplacian
    (fun z ↦ 10 ^ 10 + B z * counterexampleSeed z) w| ≤ 8 * B w
  rw [chartLaplacian_const_add]
  · calc
      _ ≤ B w * (47 / 10) + (253 / 160) * (B w / 10) + B w / 2 := hsum
      _ ≤ 8 * B w := by nlinarith [le_of_lt hBpos]
  · exact counterexampleTwoReciprocalDamping_contDiff.mul counterexampleSeed_contDiff

/-- The explicit reciprocal trace-free model is nonzero away from the reciprocal origin. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocalTraceFreeModel_ne_zero {w : ℂ} (hw : w ≠ 0) :
    let p := deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)
    let p' := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)
    traceFreeHessian counterexampleSeed w -
        8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
      4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w ≠ 0 := by
  exact seedTraceFreeHessian_perturbation_ne_zero w _ _
    (counterexampleTwoReciprocalExponent_first_bound hw)
    (counterexampleTwoReciprocalExponent_second_bound hw)

/-- The spherical trace-free Hessian of the reciprocal representative is nonzero away from
the reciprocal origin. -/
@[category API, AMS 53]
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero
    {w : ℂ} (hw : w ≠ 0) :
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w ≠ 0 := by
  rw [sphericalTraceFreeHessian_counterexampleTwoReciprocal]
  apply mul_ne_zero
  · change (counterexampleTwoReciprocalDamping w : ℂ) ≠ 0
    exact_mod_cast (by
      rw [counterexampleTwoReciprocalDamping]
      positivity : counterexampleTwoReciprocalDamping w ≠ 0)
  · exact counterexampleTwoReciprocalTraceFreeModel_ne_zero hw

/-- The spherical trace-free Hessian of the reciprocal representative is nowhere zero,
including at the reciprocal origin (the north pole of the sphere). -/
@[category API, AMS 53]
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero_all (w : ℂ) :
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w ≠ 0 := by
  by_cases hw : w = 0
  · subst w
    rw [sphericalTraceFreeHessian_counterexampleTwoReciprocal]
    apply mul_ne_zero
    · change (counterexampleTwoReciprocalDamping 0 : ℂ) ≠ 0
      exact_mod_cast (by
        rw [counterexampleTwoReciprocalDamping]
        positivity : counterexampleTwoReciprocalDamping 0 ≠ 0)
    · have hseed : traceFreeHessian counterexampleSeed 0 ≠ 0 := by
        rw [← norm_pos_iff]
        exact (by norm_num : (0 : ℝ) < 7 / 50).trans_le
          (counterexampleSeed_traceFreeHessian_norm_lower 0)
      simpa using hseed
  · exact sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero hw

/-- Uniform trace-free spherical-Hessian bound in the reciprocal chart. -/
@[category API, AMS 53]
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal_norm_upper (w : ℂ) :
    ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖ ≤
      20 * counterexampleTwoReciprocalDamping w := by
  let p := deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)
  let p' := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)
  have hp : ‖w‖ * |p| ≤ 1 / 100 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact counterexampleTwoReciprocalExponent_first_bound hw
  have hpp : ‖w‖ ^ 2 * (p ^ 2 + |p'|) ≤ 1 / 1000 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact counterexampleTwoReciprocalExponent_second_bound hw
  have hBpos : 0 < counterexampleTwoReciprocalDamping w := by
    rw [counterexampleTwoReciprocalDamping]
    positivity
  rw [sphericalTraceFreeHessian_counterexampleTwoReciprocal, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hBpos]
  change counterexampleTwoReciprocalDamping w *
      ‖traceFreeHessian counterexampleSeed w -
          8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
        4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
    20 * counterexampleTwoReciprocalDamping w
  calc
    counterexampleTwoReciprocalDamping w *
        ‖traceFreeHessian counterexampleSeed w -
            8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
          4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        counterexampleTwoReciprocalDamping w * 20 :=
      mul_le_mul_of_nonneg_left
        (seedTraceFreeHessian_perturbation_norm_upper w p p' hp hpp) hBpos.le
    _ = 20 * counterexampleTwoReciprocalDamping w := by ring

/-- The numerical coefficient in the reciprocal radius formula is below `3 · 10⁹` once the
Laplacian bound is supplied. The exact intermediate value is `2,296,000,002`. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocal_radius_coefficient_lt (w : ℂ)
    (hL : |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w) :
    ‖((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ)‖ +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 80000) *
          (‖((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ)‖ +
            ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖) <
      3000000000 := by
  have hψ : 0 ≤ counterexampleTwoReciprocalExponent (‖w‖ ^ 2) := by
    rw [counterexampleTwoReciprocalExponent]
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply mul_nonneg (Real.rpow_nonneg (sq_nonneg ‖w‖) _)
    rw [Real.flatRpowExp]
    split <;> positivity
  have hBpos : 0 < counterexampleTwoReciprocalDamping w := by
    rw [counterexampleTwoReciprocalDamping]
    positivity
  have hBle : counterexampleTwoReciprocalDamping w ≤ 1 := by
    rw [counterexampleTwoReciprocalDamping]
    have hfrac : 10000 / (‖w‖ ^ 2 + 10000) ≤ 1 := by
      apply (div_le_one₀ (by positivity)).2
      nlinarith [sq_nonneg ‖w‖]
    exact mul_le_one₀ hfrac (Real.exp_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hψ))
  have hA : ‖((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ)‖ ≤ 2 := by
    rw [counterexampleTwoReciprocal, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos hBpos]
    calc
      counterexampleTwoReciprocalDamping w * |counterexampleSeed w| ≤
          1 * (253 / 160) := mul_le_mul hBle (counterexampleSeed_abs_le w)
            (abs_nonneg _) zero_le_one
      _ ≤ 2 := by norm_num
  have hQ := sphericalTraceFreeHessian_counterexampleTwoReciprocal_norm_upper w
  have hM := reciprocalConformalDamping_bound w
  have hsum :
      ‖((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ)‖ +
          ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖ ≤
        28 * counterexampleTwoReciprocalDamping w := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  calc
    ‖((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ)‖ +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 80000) *
          (‖((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ)‖ +
            ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖) ≤
      2 + ((‖w‖ ^ 2 + 10000) ^ 2 / 80000) *
        (28 * counterexampleTwoReciprocalDamping w) := by gcongr
    _ = 2 + 14 * (((‖w‖ ^ 2 + 10000) ^ 2 / 40000) *
        counterexampleTwoReciprocalDamping w) := by ring
    _ < 2 + 14 * 164000000 := by gcongr
    _ < 3000000000 := by norm_num

/-- The exact chart formula and numerical coefficient imply the invariant radius-error bound. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocal_radius_error_bound_of_laplacian (w : ℂ)
    (hL : |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w) (v : ℂ) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let ρ := fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
    ‖fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v -
        (10 ^ 10 : ℝ) • fderiv ℝ ρ w v‖ ≤
      3000000000 * ‖fderiv ℝ ρ w v‖ := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let ρ := fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ w
  let dF : ℂ →L[ℝ] ℝ³ :=
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w
  let A : ℂ := (counterexampleTwoReciprocal w - 10 ^ 10 : ℝ)
  let L : ℂ := chartLaplacian counterexampleTwoReciprocal w
  let Q : ℂ := sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w
  let r : ℝ := (‖w‖ ^ 2 + 10000) ^ 2 / 80000
  have hscale (t : ℂ) : ‖dρ t‖ =
      200 / (‖w‖ ^ 2 + 10000) * ‖t‖ := by
    exact (counterexampleTwoReciprocalSphereChart_conformal w t t).2
  have hformula (t : ℂ) : dF t - (10 ^ 10 : ℝ) • dρ t =
      dρ (A * t + r • (L * t + Q * star t)) := by
    exact counterexampleTwoReciprocal_radius_formula w t
  have hnorm := norm_radiusError_le_of_conformal_formula dρ dF (10 ^ 10)
    (200 / (‖w‖ ^ 2 + 10000)) r A L Q (by positivity) (by positivity) hscale hformula v
  have hcoefficient := counterexampleTwoReciprocal_radius_coefficient_lt w hL
  change ‖dF v - (10 ^ 10 : ℝ) • dρ v‖ ≤ 3000000000 * ‖dρ v‖
  exact hnorm.trans (mul_le_mul_of_nonneg_right hcoefficient.le (norm_nonneg _))

/-- The derivative of a sphere-valued map into ambient Euclidean coordinates.  Naming this
transport keeps the ambient codomain visible to typeclass inference. -/
private noncomputable def sphereAmbientMfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
  mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p

/-- The reciprocal-chart radius bound transports to the intrinsic tangent space of the sphere.
No choice of tangent coordinates remains in this statement. -/
@[category API, AMS 53]
private theorem counterexampleTwo_radius_error_bound_away_south_of_laplacian
    (hL : ∀ w : ℂ, |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w)
    {p : sphere (0 : ℝ³) 1} (hp : p ≠ counterexampleSphereChart 0)
    (v : TangentSpace (𝓡 2) p) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    ‖sphereAmbientMfderiv F p v - (10 ^ 10 : ℝ) •
        sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ≤
      3000000000 *
        ‖sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  obtain ⟨w, rfl⟩ := exists_reciprocalSphereChart_of_ne_south hp
  let ρ := counterexampleTwoReciprocalSphereChart
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z : ℂ ↦ (ρ z : ℝ³)) w
  let dn : TangentSpace (𝓡 2) (ρ w) →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) (ρ w)
  let dF : TangentSpace (𝓡 2) (ρ w) →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv F (ρ w)
  have hyv : dn v ∈ (ℝ ∙ (ρ w : ℝ³))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := 2) (ρ w)]
    exact ⟨v, rfl⟩
  rw [← range_fderiv_counterexampleTwoReciprocalSphereChart w] at hyv
  obtain ⟨a, ha⟩ := hyv
  have hρmd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) ρ w :=
    counterexampleTwoReciprocalSphereChart_contMDiff.mdifferentiableAt (by simp)
  have hNmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³)
      (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) (ρ w) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³) F (ρ w) :=
    counterexampleTwoHomogeneousGradient_contMDiff.mdifferentiableAt (by simp)
  have hchainN := mfderiv_comp_apply w hNmd hρmd a
  have hchainF := mfderiv_comp_apply w hFmd hρmd a
  rw [mfderiv_eq_fderiv] at hchainN hchainF
  change dρ a = dn (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a) at hchainN
  change fderiv ℝ (fun z : ℂ ↦ F (ρ z)) w a =
    dF (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a) at hchainF
  have ha_tangent : mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a = v := by
    apply mfderiv_coe_sphere_injective (ρ w)
    change dn (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a) = dn v
    rw [← hchainN]
    simpa only [dρ, ρ] using ha
  have hchart := counterexampleTwoReciprocal_radius_error_bound_of_laplacian w (hL w) a
  change ‖fderiv ℝ (fun z : ℂ ↦ F (ρ z)) w a -
      (10 ^ 10 : ℝ) • dρ a‖ ≤ 3000000000 * ‖dρ a‖ at hchart
  change ‖dF v - (10 ^ 10 : ℝ) • dn v‖ ≤ 3000000000 * ‖dn v‖
  simpa only [hchainF, hchainN, ha_tangent] using hchart

/-- The reciprocal radius estimate gives a positive oriented radius tensor at every point away
from the south pole. This is the invariant form used for immersion and chord convexity. -/
@[category API, AMS 53]
private theorem counterexampleTwo_radius_coercive_away_south_of_laplacian
    (hL : ∀ w : ℂ, |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w)
    {p : sphere (0 : ℝ³) 1} (hp : p ≠ counterexampleSphereChart 0)
    (v : TangentSpace (𝓡 2) p) :
    7000000000 * ‖sphereAmbientMfderiv
        (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
      inner ℝ
        (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
          (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v) := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let dFv : ℝ³ := sphereAmbientMfderiv F p v
  let dnv : ℝ³ := sphereAmbientMfderiv
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v
  have herror : ‖dFv - (10 ^ 10 : ℝ) • dnv‖ ≤ 3000000000 * ‖dnv‖ :=
    counterexampleTwo_radius_error_bound_away_south_of_laplacian hL hp v
  have hcauchy : -‖dFv - (10 ^ 10 : ℝ) • dnv‖ * ‖dnv‖ ≤
      inner ℝ (dFv - (10 ^ 10 : ℝ) • dnv) dnv :=
    by
      convert neg_le_of_abs_le
        (abs_real_inner_le_norm (dFv - (10 ^ 10 : ℝ) • dnv) dnv) using 1
      all_goals ring
  have hdecompose : dFv =
      (10 ^ 10 : ℝ) • dnv + (dFv - (10 ^ 10 : ℝ) • dnv) := by module
  change 7000000000 * ‖dnv‖ ^ 2 ≤ inner ℝ dFv dnv
  rw [hdecompose, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg dnv]

/-- At the south pole, flatness of the original planar representative makes the contact-map
differential exactly the constant support value times the Gauss-map differential. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_fderiv_south :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleSphereChart z)) 0 =
      (10 ^ 10 : ℝ) •
        fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 := by
  let u := counterexample 2
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρs := counterexampleSphereChart
  let ρ : ℂ → ℝ³ := fun z ↦ (ρs z : ℝ³)
  let p := ρs 0
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ 0
  let dF : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z ↦ F (ρs z)) 0
  have hρsmooth : ContDiff ℝ ∞ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleSphereChart_contMDiff).contDiff
  have hFchartSmooth : ContDiff ℝ ∞ (fun z ↦ F (ρs z)) := by
    exact (counterexampleTwoHomogeneousGradient_contMDiff.comp
      counterexampleSphereChart_contMDiff).contDiff
  have hDρsmooth : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ ρ z) :=
    hρsmooth.fderiv_right (m := ∞) (by simp)
  have huSmooth : ContDiff ℝ ∞ u := counterexample_contDiff 2 (by omega)
  have hDuSmooth : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ u z) :=
    huSmooth.fderiv_right (m := ∞) (by simp)
  have hρrange : dρ.range = (ℝ ∙ (p : ℝ³))ᗮ := by
    simpa only [ρ, ρs, p, dρ] using range_fderiv_counterexampleSphereChart_zero
  have hpH : DifferentiableAt ℝ H (p : ℝ³) :=
    counterexampleTwoRadialExtension_differentiableAt p
  have hpcontact : inner ℝ (F p) (p : ℝ³) = (10 : ℝ) ^ 10 := by
    calc
      inner ℝ (F p) (p : ℝ³) = H p :=
        SphereSupport.inner_homogeneousGradient H p hpH
          (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
      _ = counterexampleTwoSphereExtension p := SphereSupport.radialExtension_coe _ _
      _ = u 0 := by
        dsimp only [p, ρs, u]
        rw [counterexampleTwoSphereExtension_chart]
      _ = (10 : ℝ) ^ 10 := counterexample_zero 2
  have hpullback : H ∘ ρ = u := by
    funext z
    dsimp only [Function.comp_apply, H, ρ, ρs, u]
    rw [SphereSupport.radialExtension_coe, counterexampleTwoSphereExtension_chart]
  have hfirstIdentity (z b : ℂ) :
      inner ℝ (F (ρs z)) (fderiv ℝ ρ z b) = fderiv ℝ u z b := by
    have hHz : DifferentiableAt ℝ H (ρ z) := by
      simpa only [ρ] using counterexampleTwoRadialExtension_differentiableAt (ρs z)
    have hchain := hHz.hasFDerivAt.comp z
      (hρsmooth.differentiable (by simp) z).hasFDerivAt
    rw [hpullback] at hchain
    calc
      inner ℝ (F (ρs z)) (fderiv ℝ ρ z b) =
          fderiv ℝ H (ρ z) (fderiv ℝ ρ z b) := by
        dsimp only [F]
        rw [SphereSupport.homogeneousGradient, inner_gradient_left hHz]
      _ = fderiv ℝ u z b := congr($hchain.fderiv b).symm
  have hnormalIdentity (z b : ℂ) :
      inner ℝ (ρ z) (fderiv ℝ ρ z b) = 0 := by
    have hnorm : (fun y : ℂ ↦ ‖ρ y‖ ^ 2) = fun _ ↦ (1 : ℝ) := by
      funext y
      rw [norm_eq_of_mem_sphere (ρs y)]
      norm_num
    have hderiv : fderiv ℝ (fun y : ℂ ↦ ‖ρ y‖ ^ 2) z b = 0 := by
      rw [hnorm]
      simp
    have hformula :=
      ((hρsmooth.differentiable (by simp) z).hasFDerivAt.norm_sq).fderiv
    rw [hformula] at hderiv
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply] at hderiv
    rw [two_smul] at hderiv
    linarith
  have hdu0 : fderiv ℝ u 0 = 0 := counterexample_fderiv_zero 2 (by omega)
  have hnormalP (a : ℂ) : inner ℝ (p : ℝ³) (dρ a) = 0 := by
    simpa only [p, ρ, ρs, dρ] using hnormalIdentity 0 a
  have hFp : F p = (10 ^ 10 : ℝ) • (p : ℝ³) := by
    let G : ℝ³ := (10 ^ 10 : ℝ) • (p : ℝ³)
    have hradial : inner ℝ (F p - G) (p : ℝ³) = 0 := by
      dsimp only [G]
      rw [inner_sub_left, hpcontact, real_inner_smul_left,
        real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
      norm_num
    have hmem : F p - G ∈ dρ.range := by
      rw [hρrange, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact hradial
    obtain ⟨a, ha⟩ := hmem
    have htangent : inner ℝ (F p - G) (dρ a) = 0 := by
      dsimp only [G]
      rw [inner_sub_left, real_inner_smul_left]
      have hfirst := hfirstIdentity 0 a
      change inner ℝ (F p) (dρ a) - (10 ^ 10 : ℝ) * inner ℝ (p : ℝ³) (dρ a) = 0
      rw [hfirst, hdu0]
      simp [hnormalP]
    rw [← ha] at htangent
    have htangent' : inner ℝ (dρ a) (dρ a) = 0 := htangent
    rw [real_inner_self_eq_norm_sq] at htangent'
    have haZero : dρ a = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp htangent')
    have hzero : F p - G = 0 := by
      rw [← ha]
      exact haZero
    exact sub_eq_zero.mp hzero
  have hsecondU : fderiv ℝ (fun z ↦ fderiv ℝ u z) 0 = 0 :=
    counterexample_fderiv_fderiv_zero 2 (by omega)
  apply ContinuousLinearMap.ext
  intro a
  have hradial : inner ℝ (dF a - (10 ^ 10 : ℝ) • dρ a) (p : ℝ³) = 0 := by
    have hcontactFunction : (fun z ↦ inner ℝ (F (ρs z)) (ρ z)) = u := by
      funext z
      calc
        inner ℝ (F (ρs z)) (ρ z) = H (ρs z) :=
          SphereSupport.inner_homogeneousGradient H (ρs z)
            (counterexampleTwoRadialExtension_differentiableAt (ρs z))
            (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
        _ = u z := by
          dsimp only [H, u]
          rw [SphereSupport.radialExtension_coe, counterexampleTwoSphereExtension_chart]
    have hderiv : fderiv ℝ (fun z ↦ inner ℝ (F (ρs z)) (ρ z)) 0 a = 0 := by
      rw [hcontactFunction, hdu0]
      simp
    rw [fderiv_inner_apply ℝ (hFchartSmooth.differentiable (by simp) 0)
      (hρsmooth.differentiable (by simp) 0) a] at hderiv
    change inner ℝ (F p) (dρ a) + inner ℝ (dF a) (p : ℝ³) = 0 at hderiv
    rw [hFp, real_inner_smul_left, hnormalIdentity 0 a, mul_zero, zero_add] at hderiv
    have hnormalRight : inner ℝ (dρ a) (p : ℝ³) = 0 := by
      rw [real_inner_comm]
      exact hnormalP a
    rw [inner_sub_left, real_inner_smul_left, hnormalRight, mul_zero, sub_zero]
    exact hderiv
  have hmem : dF a - (10 ^ 10 : ℝ) • dρ a ∈ dρ.range := by
    rw [hρrange, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hradial
  obtain ⟨b, hb⟩ := hmem
  have htangent : inner ℝ (dF a - (10 ^ 10 : ℝ) • dρ a) (dρ b) = 0 := by
    have hidentity : (fun z ↦ inner ℝ (F (ρs z)) (fderiv ℝ ρ z b)) =
        fun z ↦ fderiv ℝ u z b := by
      funext z
      exact hfirstIdentity z b
    have hDρb : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ ρ z b) :=
      hDρsmooth.clm_apply (show ContDiff ℝ ∞ (fun _ : ℂ ↦ b) from contDiff_const)
    have hleft := fderiv_inner_apply ℝ
      (hFchartSmooth.differentiable (by simp) 0)
      (hDρb.differentiable (by simp) 0) a
    have hright : fderiv ℝ (fun z ↦ fderiv ℝ u z b) 0 a = 0 := by
      rw [fderiv_clm_apply (hDuSmooth.differentiable (by simp) 0)
        (differentiableAt_const b : DifferentiableAt ℝ (fun _ : ℂ ↦ b) 0)]
      rw [hsecondU]
      simp
    have hderivIdentity :
        fderiv ℝ (fun z ↦ inner ℝ (F (ρs z)) (fderiv ℝ ρ z b)) 0 a = 0 := by
      rw [hidentity, hright]
    rw [hleft] at hderivIdentity
    have hnormalFunction : (fun z ↦ inner ℝ (ρ z) (fderiv ℝ ρ z b)) = fun _ ↦ 0 := by
      funext z
      exact hnormalIdentity z b
    have hnormalDerivative :
        inner ℝ (p : ℝ³) (fderiv ℝ (fun z ↦ fderiv ℝ ρ z b) 0 a) +
          inner ℝ (dρ a) (dρ b) = 0 := by
      have hzero : fderiv ℝ (fun z ↦ inner ℝ (ρ z) (fderiv ℝ ρ z b)) 0 a = 0 := by
        rw [hnormalFunction]
        simp
      rw [fderiv_inner_apply ℝ (hρsmooth.differentiable (by simp) 0)
        (hDρb.differentiable (by simp) 0) a] at hzero
      exact hzero
    change inner ℝ (F p) (fderiv ℝ (fun z ↦ fderiv ℝ ρ z b) 0 a) +
      inner ℝ (dF a) (dρ b) = 0 at hderivIdentity
    rw [hFp, real_inner_smul_left] at hderivIdentity
    rw [inner_sub_left, real_inner_smul_left]
    linarith
  rw [← hb] at htangent
  have htangent' : inner ℝ (dρ b) (dρ b) = 0 := htangent
  rw [real_inner_self_eq_norm_sq] at htangent'
  have hbZero : dρ b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp htangent')
  have hzero : dF a - (10 ^ 10 : ℝ) • dρ a = 0 := by
    rw [← hb]
    exact hbZero
  exact sub_eq_zero.mp hzero

/-- Intrinsic form of the exact south-pole radius identity. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_mfderiv_south :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    sphereAmbientMfderiv F (counterexampleSphereChart 0) =
      (10 ^ 10 : ℝ) • sphereAmbientMfderiv
        (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³)) (counterexampleSphereChart 0) := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let n : sphere (0 : ℝ³) 1 → ℝ³ := fun p ↦ (p : ℝ³)
  let dρ := mfderiv 𝓘(ℝ, ℂ) (𝓡 2) counterexampleSphereChart 0
  let dn : TangentSpace (𝓡 2) (counterexampleSphereChart 0) →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv n (counterexampleSphereChart 0)
  let dF : TangentSpace (𝓡 2) (counterexampleSphereChart 0) →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv F (counterexampleSphereChart 0)
  apply ContinuousLinearMap.ext
  intro v
  change dF v = (10 ^ 10 : ℝ) • dn v
  have hvRange : dn v ∈
      (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0).range := by
    rw [range_fderiv_counterexampleSphereChart_zero,
      ← range_mfderiv_coe_sphere (n := 2) (counterexampleSphereChart 0)]
    exact ⟨v, rfl⟩
  obtain ⟨a, ha⟩ := hvRange
  have hρmd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) counterexampleSphereChart 0 :=
    counterexampleSphereChart_contMDiff.mdifferentiableAt (by simp)
  have hNmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³) n
      (counterexampleSphereChart 0) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³) F
      (counterexampleSphereChart 0) :=
    counterexampleTwoHomogeneousGradient_contMDiff.mdifferentiableAt (by simp)
  have hchainN := mfderiv_comp_apply 0 hNmd hρmd a
  have hchainF := mfderiv_comp_apply 0 hFmd hρmd a
  rw [mfderiv_eq_fderiv] at hchainN hchainF
  change fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 a =
    dn (dρ a) at hchainN
  change fderiv ℝ (fun z : ℂ ↦ F (counterexampleSphereChart z)) 0 a =
    dF (dρ a) at hchainF
  have haTangent : dρ a = v := by
    apply mfderiv_coe_sphere_injective (counterexampleSphereChart 0)
    change dn (dρ a) = dn v
    rw [← hchainN]
    simpa only using ha
  have hsouth := congr($counterexampleTwoHomogeneousGradient_fderiv_south a)
  change fderiv ℝ (fun z : ℂ ↦ F (counterexampleSphereChart z)) 0 a =
      (10 ^ 10 : ℝ) •
        fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 a at hsouth
  rw [← haTangent, ← hchainN, ← hchainF]
  exact hsouth

/-- The south pole is an umbilic of the homogeneous-gradient contact map. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_umbilic_south :
    IsUmbilic
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0) := by
  refine ⟨(10 ^ 10 : ℝ)⁻¹, ?_⟩
  change sphereAmbientMfderiv (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³))
      (counterexampleSphereChart 0) =
    (10 ^ 10 : ℝ)⁻¹ • sphereAmbientMfderiv
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      (counterexampleSphereChart 0)
  rw [counterexampleTwoHomogeneousGradient_mfderiv_south]
  rw [smul_smul, inv_mul_cancel₀ (by norm_num : (10 ^ 10 : ℝ) ≠ 0), one_smul]

/-- Pulling an intrinsic umbilic equation through the reciprocal chart kills the anti-linear
coefficient of the chart radius tensor. -/
@[category API, AMS 53]
private theorem sphericalTraceFreeHessian_eq_zero_of_umbilic_reciprocal
    (w : ℂ)
    (humbilic : IsUmbilic
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      (fun p ↦ (p : ℝ³)) (counterexampleTwoReciprocalSphereChart w)) :
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w = 0 := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let ρ := counterexampleTwoReciprocalSphereChart
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z : ℂ ↦ (ρ z : ℝ³)) w
  let dF : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z : ℂ ↦ F (ρ z)) w
  let A : ℂ := (counterexampleTwoReciprocal w - 10 ^ 10 : ℝ)
  let L : ℂ := chartLaplacian counterexampleTwoReciprocal w
  let Q : ℂ := sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w
  let r : ℝ := (‖w‖ ^ 2 + 10000) ^ 2 / 80000
  have hdρ : Function.Injective dρ := by
    intro a b hab
    have hscale := (counterexampleTwoReciprocalSphereChart_conformal w (a - b) (a - b)).2
    change ‖dρ (a - b)‖ = 200 / (‖w‖ ^ 2 + 10000) * ‖a - b‖ at hscale
    rw [map_sub, hab, sub_self, norm_zero] at hscale
    have hpositive : 0 < 200 / (‖w‖ ^ 2 + 10000) := by positivity
    have hnormzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
  have hformula (a : ℂ) : dF a - (10 ^ 10 : ℝ) • dρ a =
      dρ (A * a + r • (L * a + Q * star a)) := by
    exact counterexampleTwoReciprocal_radius_formula w a
  have hchartUmbilic : ∃ c : ℝ, dρ = c • dF := by
    obtain ⟨c, hc⟩ := humbilic
    refine ⟨c, ?_⟩
    apply ContinuousLinearMap.ext
    intro a
    let dchart := mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w
    let dn : TangentSpace (𝓡 2) (ρ w) →L[ℝ] ℝ³ :=
      sphereAmbientMfderiv (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³)) (ρ w)
    let dFintrinsic : TangentSpace (𝓡 2) (ρ w) →L[ℝ] ℝ³ :=
      sphereAmbientMfderiv F (ρ w)
    have hρmd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) ρ w :=
      counterexampleTwoReciprocalSphereChart_contMDiff.mdifferentiableAt (by simp)
    have hNmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³)
        (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³)) (ρ w) :=
      (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
    have hFmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³) F (ρ w) :=
      counterexampleTwoHomogeneousGradient_contMDiff.mdifferentiableAt (by simp)
    have hchainN := mfderiv_comp_apply w hNmd hρmd a
    have hchainF := mfderiv_comp_apply w hFmd hρmd a
    rw [mfderiv_eq_fderiv] at hchainN hchainF
    change dρ a = dn (dchart a) at hchainN
    change dF a = dFintrinsic (dchart a) at hchainF
    have hcApply := congr($hc (dchart a))
    change dn (dchart a) = c • dFintrinsic (dchart a) at hcApply
    rw [ContinuousLinearMap.smul_apply]
    calc
      dρ a = dn (dchart a) := hchainN
      _ = c • dFintrinsic (dchart a) := hcApply
      _ = c • dF a := by rw [hchainF]
  exact antiLinearCoefficient_eq_zero_of_umbilic dρ dF hdρ (10 ^ 10) r A L Q
    (by positivity) hformula hchartUmbilic

/-- Every point other than the south pole is nonumbilic, because the reciprocal chart covers it
and its spherical trace-free Hessian is nowhere zero. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_not_umbilic_away_south
    (p : sphere (0 : ℝ³) 1) (hp : p ≠ counterexampleSphereChart 0) :
    ¬IsUmbilic
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      (fun q ↦ (q : ℝ³)) p := by
  obtain ⟨w, rfl⟩ := exists_reciprocalSphereChart_of_ne_south hp
  intro humbilic
  exact sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero_all w
    (sphericalTraceFreeHessian_eq_zero_of_umbilic_reciprocal w humbilic)

/-- The reciprocal radius estimate and the exact south-pole identity combine into global
oriented coercivity. -/
@[category API, AMS 53]
private theorem counterexampleTwo_radius_coercive_of_laplacian
    (hL : ∀ w : ℂ, |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w) :
    ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      7000000000 * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ
          (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v) := by
  intro p v
  by_cases hp : p = counterexampleSphereChart 0
  · subst p
    have hsouth := congr($counterexampleTwoHomogeneousGradient_mfderiv_south v)
    rw [hsouth]
    simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg
      ‖sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
        (counterexampleSphereChart 0) v‖]
  · exact counterexampleTwo_radius_coercive_away_south_of_laplacian hL hp v

/-- The half-space body cut out by the explicit extension is compact, convex, and
three-dimensional. -/
@[category API, AMS 53]
private theorem counterexampleTwoBody_geometry :
    Convex ℝ (SphereSupport.body counterexampleTwoSphereExtension) ∧
      IsCompact (SphereSupport.body counterexampleTwoSphereExtension) ∧
      (interior (SphereSupport.body counterexampleTwoSphereExtension)).Nonempty := by
  refine ⟨SphereSupport.body_convex _,
    SphereSupport.body_isCompact_of_continuous _
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north).continuous,
    SphereSupport.body_interior_nonempty _ zero_lt_one ?_⟩
  exact counterexampleTwoSphereExtension_lower

/-- Membership in the half-space body gives the homogeneous support inequality in every ambient
direction. -/
@[category API, AMS 53]
private theorem inner_le_counterexampleTwoRadialExtension_of_mem_body
    {x : ℝ³} (hx : x ∈ SphereSupport.body counterexampleTwoSphereExtension) (y : ℝ³) :
    inner ℝ x y ≤ SphereSupport.radialExtension counterexampleTwoSphereExtension y := by
  by_cases hy : y = 0
  · simp [hy, SphereSupport.radialExtension]
  · let q : sphere (0 : ℝ³) 1 := ⟨‖y‖⁻¹ • y, by simp [norm_smul, hy]⟩
    have hq : inner ℝ (q : ℝ³) x ≤ counterexampleTwoSphereExtension q := hx q
    have hscale : ‖y‖ * inner ℝ (q : ℝ³) x = inner ℝ x y := by
      change ‖y‖ * inner ℝ (‖y‖⁻¹ • y) x = inner ℝ x y
      rw [real_inner_smul_left, real_inner_comm]
      field_simp [norm_ne_zero_iff.mpr hy]
    calc
      inner ℝ x y = ‖y‖ * inner ℝ (q : ℝ³) x := hscale.symm
      _ ≤ ‖y‖ * counterexampleTwoSphereExtension q :=
        mul_le_mul_of_nonneg_left hq (norm_nonneg y)
      _ = SphereSupport.radialExtension counterexampleTwoSphereExtension y := by
        rw [SphereSupport.radialExtension, dif_neg hy]

/-- Differentiability of the homogeneous extension makes each exposed contact face a singleton. -/
@[category API, AMS 53]
private theorem eq_counterexampleTwoSupportPoint
    {p : sphere (0 : ℝ³) 1} {x : ℝ³}
    (hx : x ∈ SphereSupport.body counterexampleTwoSphereExtension)
    (hface : inner ℝ (p : ℝ³) x = counterexampleTwoSphereExtension p)
    (hH : DifferentiableAt ℝ
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) (p : ℝ³)) :
    x = SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) p := by
  apply SphereSupport.eq_homogeneousGradient_of_global_support _ p x hH
    (inner_le_counterexampleTwoRadialExtension_of_mem_body hx)
  simpa [real_inner_comm] using hface

/-- Convexity and differentiability of the degree-one extension supply the complete
set-theoretic support parametrization. The remaining geometric work is to verify these analytic
hypotheses and the differential properties of the resulting gradient map. -/
@[category API, AMS 53]
private theorem counterexampleTwoSupport_body_of_convex_radialExtension
    (hHdiff : ∀ p : sphere (0 : ℝ³) 1, DifferentiableAt ℝ
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) (p : ℝ³))
    (hconvex : ConvexOn ℝ univ
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    range F = frontier (SphereSupport.body counterexampleTwoSphereExtension) ∧
      IsSupportParametrization counterexampleTwoSphereExtension F
        (SphereSupport.body counterexampleTwoSphereExtension) := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  have hcontact : ∀ p, inner ℝ (F p) (p : ℝ³) = counterexampleTwoSphereExtension p := by
    intro p
    simpa [F] using SphereSupport.inner_homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) p (hHdiff p)
      (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  have hcross : ∀ (p q : sphere (0 : ℝ³) 1),
      inner ℝ (F p) (q : ℝ³) ≤ counterexampleTwoSphereExtension q := by
    intro p q
    simpa [F] using SphereSupport.inner_homogeneousGradient_le
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) p (q : ℝ³)
      hconvex (hHdiff p)
      (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  have hstationary : ∀ (p : sphere (0 : ℝ³) 1) (x : ℝ³),
      x ∈ SphereSupport.body counterexampleTwoSphereExtension →
      inner ℝ (p : ℝ³) x = counterexampleTwoSphereExtension p →
      ∀ v : ℝ³, v ∈ (ℝ ∙ (p : ℝ³))ᗮ → inner ℝ (x - F p) v = 0 := by
    intro p x hx hface v _
    rw [eq_counterexampleTwoSupportPoint hx hface (hHdiff p)]
    simp [F]
  exact ⟨SphereSupport.range_eq_frontier_of_first_variation _ F hcontact hcross
      counterexampleTwoBody_geometry.2.2 hstationary,
    SphereSupport.contact_mem_body _ F hcontact hcross⟩

/-- For the explicit radial extension, the homogeneous-gradient differential is tangent to the
sphere. This follows directly by differentiating Euler's identity and does not use support
convexity. -/
@[category API, AMS 53]
private theorem counterexampleTwoHomogeneousGradient_normal :
    ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      inner ℝ (p : ℝ³)
        (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
          (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v) = 0 := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let G : ℝ³ → ℝ³ := gradient H
  let F := SphereSupport.homogeneousGradient H
  have hHsmooth : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
  have hGsmooth : ContDiffOn ℝ ∞ G {0}ᶜ := by
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
      hHsmooth.fderiv_of_isOpen isOpen_compl_singleton (by simp)
    simpa only [G, gradient] using
      (InnerProductSpace.toDual ℝ ℝ³).symm.contDiff.comp_contDiffOn hDf
  have hEuler (x : ℝ³) (hx : x ≠ 0) : inner ℝ (G x) x = H x := by
    have hHdiff : DifferentiableAt ℝ H x :=
      (hHsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
        (isOpen_compl_singleton.mem_nhds hx)
    dsimp only [G]
    rw [inner_gradient_left hHdiff]
    have hline : HasDerivAt (fun t : ℝ ↦ H (x + t • x)) (fderiv ℝ H x x) 0 := by
      have harg : HasDerivAt (fun t : ℝ ↦ x + t • x) x 0 := by
        simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using
          (hasDerivAt_const (x := (0 : ℝ)) x).add
            ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const x)
      simpa [Function.comp_def] using
        hHdiff.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
    have heq : (fun t : ℝ ↦ H (x + t • x)) =ᶠ[nhds 0]
        fun t ↦ (1 + t) * H x := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      calc
        H (x + t • x) = H ((1 + t) • x) := by rw [add_smul, one_smul]
        _ = (1 + t) * H x := SphereSupport.radialExtension_smul_of_pos _ _
          (by linarith [(abs_lt.mp ht).1])
    have hright : HasDerivAt (fun t : ℝ ↦ (1 + t) * H x) (H x) 0 := by
      convert (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1 |>.mul_const (H x) using 1
      all_goals ring
    exact (hline.congr_of_eventuallyEq heq.symm).unique hright
  intro p v
  have hp : (p : ℝ³) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hpG : DifferentiableAt ℝ G (p : ℝ³) :=
    (hGsmooth (p : ℝ³) hp).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hp)
  have hpH : DifferentiableAt ℝ H (p : ℝ³) :=
    (hHsmooth (p : ℝ³) hp).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hp)
  have hEulerEventually : (fun x : ℝ³ ↦ inner ℝ (G x) x) =ᶠ[nhds (p : ℝ³)] H := by
    filter_upwards [eventually_ne_nhds hp] with x hx
    exact hEuler x hx
  have hnormalAmbient (a : ℝ³) :
      inner ℝ (p : ℝ³) (fderiv ℝ G (p : ℝ³) a) = 0 := by
    have hderivEq := hEulerEventually.fderiv_eq (𝕜 := ℝ)
    have happ := congr($hderivEq a)
    change (fderiv ℝ (fun t : ℝ³ ↦ inner ℝ (G t) (id t)) (p : ℝ³)) a =
      (fderiv ℝ H (p : ℝ³)) a at happ
    rw [fderiv_inner_apply ℝ hpG differentiableAt_id a,
      inner_gradient_left hpH] at happ
    simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at happ
    rw [real_inner_comm]
    linarith
  have hchain := mfderiv_comp_apply p
    (hpG.mdifferentiableAt)
    ((contMDiff_coe_sphere (m := ∞) p).mdifferentiableAt (by simp)) v
  rw [mfderiv_eq_fderiv] at hchain
  change sphereAmbientMfderiv F p v =
      fderiv ℝ G (p : ℝ³)
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v) at hchain
  rw [hchain]
  exact hnormalAmbient _

/-- Intrinsic radius-tensor coercivity is the ambient Hessian lower bound for the degree-one
radial extension. Only the tangential component of the ambient direction contributes. -/
@[category API, AMS 53]
private theorem counterexampleTwoRadialExtension_hessian_coercive
    (hCoercive : ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      7000000000 * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ
          (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v))
    {x d : ℝ³} (hx : x ≠ 0) :
    let p : sphere (0 : ℝ³) 1 := ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩
    let τ := d - inner ℝ d (p : ℝ³) • (p : ℝ³)
    7000000000 / ‖x‖ * ‖τ‖ ^ 2 ≤
      inner ℝ
        (fderiv ℝ
          (gradient (SphereSupport.radialExtension counterexampleTwoSphereExtension)) x d) d := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let G : ℝ³ → ℝ³ := gradient H
  let F := SphereSupport.homogeneousGradient H
  let r := ‖x‖
  let p : sphere (0 : ℝ³) 1 := ⟨r⁻¹ • x, by simp [r, norm_smul, hx]⟩
  let τ : ℝ³ := d - inner ℝ d (p : ℝ³) • (p : ℝ³)
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hHsmooth : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
  have hGsmooth : ContDiffOn ℝ ∞ G {0}ᶜ := by
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
      hHsmooth.fderiv_of_isOpen isOpen_compl_singleton (by simp)
    simpa only [G, gradient] using
      (InnerProductSpace.toDual ℝ ℝ³).symm.contDiff.comp_contDiffOn hDf
  have hGscale (y : ℝ³) (hy : y ≠ 0) (a : ℝ) (ha : 0 < a) :
      G (a • y) = G y := by
    have hay : a • y ≠ 0 := smul_ne_zero ha.ne' hy
    have hyH : DifferentiableAt ℝ H y :=
      (hHsmooth y hy).differentiableWithinAt (by simp) |>.differentiableAt
        (isOpen_compl_singleton.mem_nhds hy)
    have hayH : DifferentiableAt ℝ H (a • y) :=
      (hHsmooth (a • y) hay).differentiableWithinAt (by simp) |>.differentiableAt
        (isOpen_compl_singleton.mem_nhds hay)
    apply ext_inner_right ℝ
    intro z
    dsimp only [G]
    rw [inner_gradient_left hayH, inner_gradient_left hyH]
    have harg : HasFDerivAt (fun z : ℝ³ ↦ a • z)
        (a • ContinuousLinearMap.id ℝ ℝ³) y := by fun_prop
    have hleft := hayH.hasFDerivAt.comp y harg
    change HasFDerivAt (fun z : ℝ³ ↦ H (a • z))
      ((fderiv ℝ H (a • y)).comp (a • ContinuousLinearMap.id ℝ ℝ³)) y at hleft
    have hright := hyH.hasFDerivAt.const_smul a
    have heq : (fun z : ℝ³ ↦ H (a • z)) = fun z ↦ a • H z := by
      funext z
      simpa only [smul_eq_mul] using SphereSupport.radialExtension_smul_of_pos
        counterexampleTwoSphereExtension z ha
    rw [heq] at hleft
    have hderivEq := hleft.unique hright
    have happ := congr($hderivEq z)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at happ
    exact (mul_left_cancel₀ ha.ne' happ)
  have hp0 : (p : ℝ³) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hpG : DifferentiableAt ℝ G (p : ℝ³) :=
    (hGsmooth (p : ℝ³) hp0).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hp0)
  have hxG : DifferentiableAt ℝ G x :=
    (hGsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hx)
  have hradialKernel : fderiv ℝ G (p : ℝ³) (p : ℝ³) = 0 := by
    have hline : HasDerivAt (fun t : ℝ ↦ G ((p : ℝ³) + t • (p : ℝ³)))
        (fderiv ℝ G (p : ℝ³) (p : ℝ³)) 0 := by
      have harg : HasDerivAt (fun t : ℝ ↦ (p : ℝ³) + t • (p : ℝ³))
          (p : ℝ³) 0 := by
        simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using
          (hasDerivAt_const (x := (0 : ℝ)) (p : ℝ³)).add
            ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (p : ℝ³))
      simpa [Function.comp_def] using
        hpG.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
    have heq : (fun t : ℝ ↦ G ((p : ℝ³) + t • (p : ℝ³))) =ᶠ[nhds 0]
        fun _ ↦ G (p : ℝ³) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      rw [show (p : ℝ³) + t • (p : ℝ³) = (1 + t) • (p : ℝ³) by
        rw [add_smul, one_smul]]
      exact hGscale (p : ℝ³) hp0 (1 + t) (by linarith [(abs_lt.mp ht).1])
    have hzero : HasDerivAt (fun _ : ℝ ↦ G (p : ℝ³)) 0 0 := hasDerivAt_const 0 _
    exact (hline.congr_of_eventuallyEq heq.symm).unique hzero
  have hscaleHessian (z : ℝ³) :
      fderiv ℝ G x z = r⁻¹ • fderiv ℝ G (p : ℝ³) z := by
    have hrp : r • (p : ℝ³) = x := by
      dsimp only [p]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hxG' : DifferentiableAt ℝ G (r • (p : ℝ³)) := by
      simpa only [hrp] using hxG
    have harg : HasFDerivAt (fun y : ℝ³ ↦ r • y)
        (r • ContinuousLinearMap.id ℝ ℝ³) (p : ℝ³) := by fun_prop
    have hleft := hxG'.hasFDerivAt.comp (p : ℝ³) harg
    have heq : (fun y : ℝ³ ↦ G (r • y)) =ᶠ[nhds (p : ℝ³)] G := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hp0] with y hy
      exact hGscale y hy r hr
    have hderivEq := (hleft.congr_of_eventuallyEq heq.symm).unique hpG.hasFDerivAt
    have happ := congr($hderivEq (r⁻¹ • z))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
      map_smul] at happ
    simpa only [hrp] using happ
  have hτ : τ ∈ (ℝ ∙ (p : ℝ³))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    dsimp only [τ]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere p]
    ring
  rw [← range_mfderiv_coe_sphere (n := 2) p] at hτ
  obtain ⟨v, hv⟩ := hτ
  let dn : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv F p
  have hchain := mfderiv_comp_apply p hpG.mdifferentiableAt
    ((contMDiff_coe_sphere (m := ∞) p).mdifferentiableAt (by simp)) v
  rw [mfderiv_eq_fderiv] at hchain
  change dF v = fderiv ℝ G (p : ℝ³) (dn v) at hchain
  have hv' : dn v = τ := by
    simpa only [dn, sphereAmbientMfderiv] using hv
  have hddecomp : d = inner ℝ d (p : ℝ³) • (p : ℝ³) + τ := by
    dsimp only [τ]
    module
  have hGp_d : fderiv ℝ G (p : ℝ³) d = dF v := by
    rw [hddecomp, map_add, map_smul, hradialKernel, smul_zero, zero_add, ← hv', ← hchain]
  have hnormal : inner ℝ (dF v) (p : ℝ³) = 0 := by
    rw [real_inner_comm]
    exact counterexampleTwoHomogeneousGradient_normal p v
  have hinner : inner ℝ (fderiv ℝ G x d) d =
      r⁻¹ * inner ℝ (dF v) (dn v) := by
    rw [hscaleHessian, hGp_d, hddecomp, inner_add_right]
    simp only [real_inner_smul_left, real_inner_smul_right, hnormal, mul_zero, zero_add]
    rw [← hv']
  rw [hinner]
  have hbase := hCoercive p v
  have hrinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  calc
    7000000000 / ‖x‖ * ‖τ‖ ^ 2 =
        r⁻¹ * (7000000000 * ‖dn v‖ ^ 2) := by rw [← hv']; dsimp only [r]; ring
    _ ≤ r⁻¹ * inner ℝ (dF v) (dn v) := mul_le_mul_of_nonneg_left hbase hrinv

/-- Contact and cross-support represent the homogeneous extension as a supremum of linear
functionals, and therefore make it convex. -/
@[category API, AMS 53]
private theorem counterexampleTwoRadialExtension_convex_of_cross
    (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hcontact : ∀ p : sphere (0 : ℝ³) 1,
      inner ℝ (F p) (p : ℝ³) = counterexampleTwoSphereExtension p)
    (hcross : ∀ (p q : sphere (0 : ℝ³) 1),
      inner ℝ (F p) (q : ℝ³) ≤ counterexampleTwoSphereExtension q) :
    ConvexOn ℝ univ (SphereSupport.radialExtension counterexampleTwoSphereExtension) := by
  have hFbody : ∀ p, F p ∈ SphereSupport.body counterexampleTwoSphereExtension := fun p ↦
    (SphereSupport.contact_mem_body counterexampleTwoSphereExtension F hcontact hcross p).1
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hz : a • x + b • y = 0
  · rw [hz]
    simp only [SphereSupport.radialExtension, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (counterexampleTwoRadialExtension_nonneg x))
      (mul_nonneg hb (counterexampleTwoRadialExtension_nonneg y))
  · let q : sphere (0 : ℝ³) 1 :=
      ⟨‖a • x + b • y‖⁻¹ • (a • x + b • y), by
        rw [mem_sphere]
        simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    have hrepresentation :
        SphereSupport.radialExtension counterexampleTwoSphereExtension (a • x + b • y) =
          inner ℝ (F q) (a • x + b • y) := by
      rw [SphereSupport.radialExtension, dif_neg hz]
      change ‖a • x + b • y‖ * counterexampleTwoSphereExtension q = _
      rw [← hcontact q, real_inner_smul_right]
      field_simp [norm_ne_zero_iff.mpr hz]
    rw [hrepresentation, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      smul_eq_mul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (inner_le_counterexampleTwoRadialExtension_of_mem_body (hFbody q) x) ha)
      (mul_le_mul_of_nonneg_left
        (inner_le_counterexampleTwoRadialExtension_of_mem_body (hFbody q) y) hb)

/-- Positive oriented coercivity relative to an injective reference map implies injectivity. -/
@[category API, AMS 53]
private theorem continuousLinearMap_injective_of_coercive
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (N L : E →L[ℝ] F)
    (hN : Function.Injective N) {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖N v‖ ^ 2 ≤ inner ℝ (L v) (N v)) : Function.Injective L := by
  intro v w hvw
  have hzero : L (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hbound := hL (v - w)
  rw [hzero, inner_zero_left] at hbound
  have hnormsq : ‖N (v - w)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖N (v - w)‖]
  have : N (v - w) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)
  rw [map_sub] at this
  exact hN (sub_eq_zero.mp this)

/-- Oriented coercivity of the radius tensor makes the degree-one extension strictly convex
along every chord that does not pass through the origin. -/
@[category API, AMS 53]
private theorem counterexampleTwoRadialExtension_strictConvexOn_chord
    (hCoercive : ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      7000000000 * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ
          (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v))
    (p q : sphere (0 : ℝ³) 1) (hpq : p ≠ q)
    (hantipodal : (q : ℝ³) ≠ -(p : ℝ³)) :
    StrictConvexOn ℝ (Icc 0 1) (fun t : ℝ ↦
      SphereSupport.radialExtension counterexampleTwoSphereExtension
        ((p : ℝ³) + t • ((q : ℝ³) - (p : ℝ³)))) := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let G : ℝ³ → ℝ³ := gradient H
  let d : ℝ³ := (q : ℝ³) - (p : ℝ³)
  let line : ℝ → ℝ³ := fun t ↦ (p : ℝ³) + t • d
  let f : ℝ → ℝ := fun t ↦ H (line t)
  have hline_ne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : line t ≠ 0 := by
    intro hzero
    have heq : t • (q : ℝ³) = -(1 - t) • (p : ℝ³) := by
      dsimp only [line, d] at hzero
      have hzero' : (1 - t) • (p : ℝ³) + t • (q : ℝ³) = 0 := by
        calc
          (1 - t) • (p : ℝ³) + t • (q : ℝ³) =
              (p : ℝ³) + t • ((q : ℝ³) - (p : ℝ³)) := by module
          _ = 0 := hzero
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_right hzero'
    have hnorm := congrArg norm heq
    simp only [norm_smul, norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q, mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg ht.1,
      abs_of_nonneg (sub_nonneg.mpr ht.2)] at hnorm
    have htHalf : t = 1 / 2 := by linarith
    apply hantipodal
    rw [htHalf] at heq
    norm_num at heq
    have heq' : (1 / 2 : ℝ) • (q : ℝ³) = (1 / 2 : ℝ) • (-(p : ℝ³)) := by
      simpa only [smul_neg] using heq
    have h := congrArg (fun z : ℝ³ ↦ (2 : ℝ) • z) heq'
    norm_num [smul_smul] at h
    exact h
  have hHsmooth : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
  have hGsmooth : ContDiffOn ℝ ∞ G {0}ᶜ := by
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
      hHsmooth.fderiv_of_isOpen isOpen_compl_singleton (by simp)
    simpa only [G, gradient] using
      (InnerProductSpace.toDual ℝ ℝ³).symm.contDiff.comp_contDiffOn hDf
  apply strictConvexOn_of_deriv2_pos' (convex_Icc 0 1)
  · intro t ht
    have hlineCont : ContinuousAt line t := by fun_prop
    exact ((hHsmooth (line t) (hline_ne t ht)).contDiffAt
      (isOpen_compl_singleton.mem_nhds (hline_ne t ht))).continuousAt
      |>.comp_continuousWithinAt hlineCont.continuousWithinAt
  · intro t ht
    let x := line t
    let r := ‖x‖
    let s : sphere (0 : ℝ³) 1 := ⟨r⁻¹ • x, by
      simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm, r]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hline_ne t ht))⟩
    let τ : ℝ³ := d - inner ℝ d (s : ℝ³) • (s : ℝ³)
    have hx : x ≠ 0 := hline_ne t ht
    have hr : 0 < r := norm_pos_iff.mpr hx
    let c : ℝ := inner ℝ (p : ℝ³) (q : ℝ³)
    have hcUpper : c ≤ 1 :=
      real_inner_le_one_of_norm_eq_one (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere q)
    have hcLower : -1 ≤ c := by
      have := real_inner_le_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
        (norm_neg (q : ℝ³) ▸ norm_eq_of_mem_sphere q)
      rw [inner_neg_right] at this
      dsimp only [c]
      linarith
    have hcneOne : c ≠ 1 := by
      dsimp only [c]
      intro h
      have hpq' : (p : ℝ³) = (q : ℝ³) :=
        (inner_eq_one_iff_of_norm_eq_one (norm_eq_of_mem_sphere p)
          (norm_eq_of_mem_sphere q)).mp h
      exact hpq (Subtype.ext hpq')
    have hcneNegOne : c ≠ -1 := by
      dsimp only [c]
      intro h
      have hpnegq : (p : ℝ³) = -(q : ℝ³) :=
        (inner_eq_neg_one_iff_of_norm_eq_one (norm_eq_of_mem_sphere p)
          (norm_eq_of_mem_sphere q)).mp h
      apply hantipodal
      have h' := congrArg Neg.neg hpnegq
      simpa using h'.symm
    have hcpos : 0 < 1 - c ^ 2 := by
      rcases lt_or_eq_of_le hcUpper with hc | hc
      · rcases lt_or_eq_of_le hcLower with hc' | hc'
        · nlinarith
        · exact (hcneNegOne hc'.symm).elim
      · exact (hcneOne hc).elim
    have hgram : r ^ 2 * ‖τ‖ ^ 2 = 1 - c ^ 2 := by
      have hxexpr : x = (1 - t) • (p : ℝ³) + t • (q : ℝ³) := by
        dsimp only [x, line, d]
        module
      have hrsq : r ^ 2 = (1 - t) ^ 2 + t ^ 2 +
          2 * t * (1 - t) * c := by
        dsimp only [r]
        rw [← real_inner_self_eq_norm_sq x, hxexpr]
        dsimp only [c]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, real_inner_self_eq_norm_sq,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2),
          abs_of_nonneg ht.1, norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q, mul_one]
        rw [real_inner_comm (q : ℝ³) (p : ℝ³)]
        ring
      have hdsq : ‖d‖ ^ 2 = 2 - 2 * c := by
        rw [← real_inner_self_eq_norm_sq d]
        dsimp only [d, c]
        simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
          norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q]
        rw [real_inner_comm (q : ℝ³) (p : ℝ³)]
        ring
      have hdx : inner ℝ d x = (2 * t - 1) * (1 - c) := by
        rw [hxexpr]
        dsimp only [d, c]
        simp only [inner_sub_left, inner_add_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p,
          norm_eq_of_mem_sphere q]
        rw [real_inner_comm (q : ℝ³) (p : ℝ³)]
        ring
      have hds : inner ℝ d (s : ℝ³) = r⁻¹ * inner ℝ d x := by
        dsimp only [s]
        rw [real_inner_smul_right]
      have hτsq : ‖τ‖ ^ 2 = ‖d‖ ^ 2 - inner ℝ d (s : ℝ³) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq τ]
        dsimp only [τ]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right, real_inner_self_eq_norm_sq]
        rw [real_inner_comm (s : ℝ³) d, norm_smul, norm_eq_of_mem_sphere s,
          mul_one, Real.norm_eq_abs, sq_abs]
        ring
      rw [hτsq, hds, hdsq, hdx]
      field_simp [hr.ne']
      nlinarith [hrsq]
    have hτ : τ ≠ 0 := by
      intro hτzero
      rw [hτzero, norm_zero] at hgram
      nlinarith
    have hsecond : (deriv^[2] f) t = inner ℝ (fderiv ℝ G x d) d := by
      have hlineDeriv : HasDerivAt line d t := by
        dsimp only [line]
        simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using
          (hasDerivAt_const (x := t) (p : ℝ³)).add
            ((hasDerivAt_id (𝕜 := ℝ) t).smul_const d)
      have hxH : DifferentiableAt ℝ H x :=
        (hHsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
          (isOpen_compl_singleton.mem_nhds hx)
      have hxG : DifferentiableAt ℝ G x :=
        (hGsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
          (isOpen_compl_singleton.mem_nhds hx)
      have hfirst : deriv f =ᶠ[nhds t] fun y ↦ inner ℝ (G (line y)) d := by
        have hlineEvent : ∀ᶠ y in nhds t, line y ≠ 0 := by
          exact (by fun_prop : ContinuousAt line t).eventually_ne (by simpa [x] using hx)
        filter_upwards [hlineEvent] with y hy
        have hyH : DifferentiableAt ℝ H (line y) :=
          (hHsmooth (line y) hy).differentiableWithinAt (by simp) |>.differentiableAt
            (isOpen_compl_singleton.mem_nhds hy)
        have hyline : HasDerivAt line d y := by
          dsimp only [line]
          simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using
            (hasDerivAt_const (x := y) (p : ℝ³)).add
              ((hasDerivAt_id (𝕜 := ℝ) y).smul_const d)
        rw [(by simpa [Function.comp_def] using
          hyH.hasFDerivAt.comp_hasDerivAt_of_eq (x := y) hyline rfl :
            HasDerivAt f (fderiv ℝ H (line y) d) y).deriv]
        dsimp only [G]
        rw [inner_gradient_left hyH]
      change deriv (deriv f) t = inner ℝ (fderiv ℝ G x d) d
      rw [hfirst.deriv_eq]
      have hGline : HasDerivAt (fun y ↦ G (line y)) (fderiv ℝ G x d) t := by
        simpa [Function.comp_def, x] using
          hxG.hasFDerivAt.comp_hasDerivAt_of_eq (x := t) hlineDeriv rfl
      simpa using (hGline.inner ℝ (hasDerivAt_const t d)).deriv
    rw [hsecond]
    have hbound := counterexampleTwoRadialExtension_hessian_coercive
      (x := x) (d := d) hCoercive hx
    change 7000000000 / ‖x‖ * ‖τ‖ ^ 2 ≤ inner ℝ (fderiv ℝ G x d) d at hbound
    exact lt_of_lt_of_le
      (mul_pos (div_pos (by norm_num) hr) (sq_pos_of_pos (norm_pos_iff.mpr hτ))) hbound

/-- Strict convexity of the homogeneous extension on each nonradial chord gives strict
cross-support. The antipodal chord is handled directly by positivity of the support values. -/
@[category API, AMS 53]
private theorem strictCross_of_strictConvex_chords
    (h : sphere (0 : ℝ³) 1 → ℝ) (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hHdiff : ∀ p : sphere (0 : ℝ³) 1,
      DifferentiableAt ℝ (SphereSupport.radialExtension h) (p : ℝ³))
    (hF : F = SphereSupport.homogeneousGradient (SphereSupport.radialExtension h))
    (hlower : ∀ p, 1 ≤ h p)
    (hchord : ∀ (p q : sphere (0 : ℝ³) 1), p ≠ q → (q : ℝ³) ≠ -(p : ℝ³) →
      StrictConvexOn ℝ (Icc 0 1) (fun t : ℝ ↦
        SphereSupport.radialExtension h ((p : ℝ³) + t • ((q : ℝ³) - (p : ℝ³))))) :
    ∀ (p q : sphere (0 : ℝ³) 1), p ≠ q → inner ℝ (F p) (q : ℝ³) < h q := by
  subst F
  intro p q hpq
  have hcontact : inner ℝ
      (SphereSupport.homogeneousGradient (SphereSupport.radialExtension h) p)
      (p : ℝ³) = h p := by
    simpa using SphereSupport.inner_homogeneousGradient
      (SphereSupport.radialExtension h) p (hHdiff p)
        (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  by_cases hantipodal : (q : ℝ³) = -(p : ℝ³)
  · rw [hantipodal, inner_neg_right, hcontact]
    linarith [hlower p, hlower q]
  · let line : ℝ → ℝ³ := fun t ↦ (p : ℝ³) + t • ((q : ℝ³) - (p : ℝ³))
    let f : ℝ → ℝ := fun t ↦ SphereSupport.radialExtension h (line t)
    have hline : HasDerivAt f
        (fderiv ℝ (SphereSupport.radialExtension h) (p : ℝ³)
          ((q : ℝ³) - (p : ℝ³))) 0 := by
      have harg : HasDerivAt line ((q : ℝ³) - (p : ℝ³)) 0 := by
        simpa only [line, Pi.add_apply, id_eq, zero_add, one_smul] using
          (hasDerivAt_const (x := (0 : ℝ)) (p : ℝ³)).add
            ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const ((q : ℝ³) - (p : ℝ³)))
      simpa [f, Function.comp_def] using
        (hHdiff p).hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp [line])
    have hslope := (hchord p q hpq hantipodal).deriv_lt_slope
      (by simp) (by simp) zero_lt_one hline.differentiableAt
    rw [hline.deriv] at hslope
    have hslope' : fderiv ℝ (SphereSupport.radialExtension h) (p : ℝ³)
        ((q : ℝ³) - (p : ℝ³)) < h q - h p := by
      simpa [f, line, slope] using hslope
    rw [← inner_gradient_left (hHdiff p)] at hslope'
    change inner ℝ
      (SphereSupport.homogeneousGradient (SphereSupport.radialExtension h) p)
        ((q : ℝ³) - (p : ℝ³)) < h q - h p at hslope'
    rw [inner_sub_right, hcontact] at hslope'
    linarith

/-- Global oriented coercivity yields the strict support inequality for distinct normals. -/
@[category API, AMS 53]
private theorem counterexampleTwo_strictCross_of_coercive
    (hCoercive : ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      7000000000 * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ
          (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v)) :
    ∀ (p q : sphere (0 : ℝ³) 1), p ≠ q →
      inner ℝ
        (SphereSupport.homogeneousGradient
          (SphereSupport.radialExtension counterexampleTwoSphereExtension) p)
        (q : ℝ³) < counterexampleTwoSphereExtension q := by
  exact strictCross_of_strictConvex_chords counterexampleTwoSphereExtension
    (SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension))
    counterexampleTwoRadialExtension_differentiableAt rfl
    counterexampleTwoSphereExtension_lower
    (fun p q hpq hantipodal ↦
      counterexampleTwoRadialExtension_strictConvexOn_chord
        hCoercive p q hpq hantipodal)

/-- The explicit seed Laplacian estimate closes the reciprocal radius certificate. -/
@[category API, AMS 53]
private theorem counterexampleTwoReciprocal_chartLaplacian_bound (w : ℂ) :
    |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w := by
  exact chartLaplacian_counterexampleTwoReciprocal_le_of_seed
    counterexampleSeed_chartLaplacian_abs_le w

/-- The exact analytic certificate needed to finish the support geometry once the explicit
radius-tensor estimates have been established. -/
@[category API, AMS 53]
private theorem counterexampleTwoSupport_geometry_of_certificates
    (hCoercive : ∀ p v, 7000000000 *
      ‖sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
      inner ℝ (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v))
    (hstrict : ∀ (p q : sphere (0 : ℝ³) 1), p ≠ q →
      inner ℝ (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension) p) (q : ℝ³) <
          counterexampleTwoSphereExtension q)
    (humbilic : IsUmbilic
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0))
    (hnoUmbilic : ∀ p, p ≠ counterexampleSphereChart 0 → ¬IsUmbilic
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      (fun q ↦ (q : ℝ³)) p) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let K := SphereSupport.body counterexampleTwoSphereExtension
    IsConvexSphereOfClass ∞ F (fun p ↦ (p : ℝ³)) ∧
      Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      range F = frontier K ∧
      IsSupportParametrization counterexampleTwoSphereExtension F K ∧
      IsUmbilic F (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0) ∧
      ∀ p, IsUmbilic F (fun q ↦ (q : ℝ³)) p → p = counterexampleSphereChart 0 := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let K := SphereSupport.body counterexampleTwoSphereExtension
  have hHdiff : ∀ p : sphere (0 : ℝ³) 1, DifferentiableAt ℝ
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) (p : ℝ³) :=
    counterexampleTwoRadialExtension_differentiableAt
  have hFsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) ∞ F := by
    exact counterexampleTwoHomogeneousGradient_contMDiff
  change ∀ p v, 7000000000 *
      ‖sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
      inner ℝ (sphereAmbientMfderiv F p v)
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v) at hCoercive
  have hFinjective : ∀ p : sphere (0 : ℝ³) 1, Function.Injective
      (sphereAmbientMfderiv F p) := fun p ↦
    continuousLinearMap_injective_of_coercive _ _
      (mfderiv_coe_sphere_injective p) (by norm_num) (hCoercive p)
  change ∀ (p q : sphere (0 : ℝ³) 1), p ≠ q →
    inner ℝ (F p) (q : ℝ³) < counterexampleTwoSphereExtension q at hstrict
  change IsUmbilic F (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0) at humbilic
  change ∀ p, p ≠ counterexampleSphereChart 0 →
    ¬IsUmbilic F (fun q ↦ (q : ℝ³)) p at hnoUmbilic
  have hunique : ∀ p, IsUmbilic F (fun q ↦ (q : ℝ³)) p →
      p = counterexampleSphereChart 0 := by
    intro p hp
    by_contra hp0
    exact hnoUmbilic p hp0 hp
  have hcontact : ∀ p : sphere (0 : ℝ³) 1,
      inner ℝ (F p) (p : ℝ³) = counterexampleTwoSphereExtension p := by
    intro p
    simpa [F] using SphereSupport.inner_homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) p (hHdiff p)
      (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  have hcross : ∀ p q : sphere (0 : ℝ³) 1,
      inner ℝ (F p) (q : ℝ³) ≤ counterexampleTwoSphereExtension q := by
    intro p q
    by_cases hpq : p = q
    · subst q
      exact (hcontact p).le
    · exact (hstrict p q hpq).le
  have hconvex : ConvexOn ℝ univ
      (SphereSupport.radialExtension counterexampleTwoSphereExtension) :=
    counterexampleTwoRadialExtension_convex_of_cross F hcontact hcross
  have hbody := counterexampleTwoSupport_body_of_convex_radialExtension hHdiff hconvex
  change range F = frontier K ∧
    IsSupportParametrization counterexampleTwoSphereExtension F K at hbody
  have hnormal : ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      inner ℝ (p : ℝ³) (sphereAmbientMfderiv F p v) = 0 :=
    counterexampleTwoHomogeneousGradient_normal
  have hK := counterexampleTwoBody_geometry
  refine ⟨⟨hFsmooth,
      SphereSupport.isEmbedding_of_strictCross _ F hFsmooth.continuous hcontact hstrict,
      hFinjective, contMDiff_coe_sphere, (fun p ↦ norm_eq_of_mem_sphere p), hnormal,
      ⟨K, hK.1, hK.2.1, hK.2.2, hbody.1⟩⟩,
    hK.1, hK.2.1, hK.2.2, hbody.1, hbody.2, humbilic, hunique⟩

/-- A smooth spherical extension of `counterexample 2` is the support function of a
convex body whose Gauss parametrization has exactly one umbilic. -/
@[category research solved, AMS 52 53]
theorem counterexample_two_support_geometry
    (h : sphere (0 : ℝ³) 1 → ℝ)
    (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hchart : ∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) :
    ∃ (F : sphere (0 : ℝ³) 1 → ℝ³) (K : Set ℝ³),
      IsConvexSphereOfClass ∞ F (fun p ↦ (p : ℝ³)) ∧
      Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      Set.range F = frontier K ∧ IsSupportParametrization h F K ∧
      IsUmbilic F (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0) ∧
      ∀ p, IsUmbilic F (fun q ↦ (q : ℝ³)) p → p = counterexampleSphereChart 0 := by
  have hextension := eq_counterexampleTwoSphereExtension h hsmooth hchart
  subst h
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let K := SphereSupport.body counterexampleTwoSphereExtension
  have hCoercive := counterexampleTwo_radius_coercive_of_laplacian
    counterexampleTwoReciprocal_chartLaplacian_bound
  have hstrict := counterexampleTwo_strictCross_of_coercive hCoercive
  refine ⟨F, K, ?_⟩
  simpa only [F, K] using counterexampleTwoSupport_geometry_of_certificates
    hCoercive hstrict counterexampleTwoHomogeneousGradient_umbilic_south
      counterexampleTwoHomogeneousGradient_not_umbilic_away_south

/-- **Alpöge's smooth Carathéodory counterexample.**

The function `counterexample 2` extends across the omitted north pole to a smooth function `h`
on the round two-sphere. It is the support function of a convex body `K`; `F` is its smooth
Gauss parametrization with outward normal `p`. The corresponding convex surface has exactly one
umbilic, at the point represented by `z = 0`.

The explicit compactness and nonempty-interior conditions rule out unbounded and
lower-dimensional convex sets. The range equality ensures that `F` parametrizes the boundary
of the same body whose support function is `h`. -/
@[category research solved, AMS 52 53]
theorem counterexample_two_is_support_function_with_unique_umbilic :
    ∃ (h : sphere (0 : ℝ³) 1 → ℝ) (F : sphere (0 : ℝ³) 1 → ℝ³) (K : Set ℝ³),
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) ∧
      IsConvexSphereOfClass ∞ F (fun p ↦ (p : ℝ³)) ∧
      Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      Set.range F = frontier K ∧ IsSupportParametrization h F K ∧
      IsUmbilic F (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0) ∧
      ∀ p, IsUmbilic F (fun q ↦ (q : ℝ³)) p → p = counterexampleSphereChart 0 := by
  rcases counterexample_two_sphere_extension with ⟨h, hsmooth, hchart⟩
  rcases counterexample_two_support_geometry h hsmooth hchart with ⟨F, K, hgeometry⟩
  exact ⟨h, F, K, hsmooth, hchart, hgeometry⟩

end CaratheodoryLoewnerCounterexample
