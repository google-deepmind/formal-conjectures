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


import AEGISOverlay.RHWeilTiltComplementarityV1
import RestrictedWeilCriterionResidueCoefficientV11

/-!
# One moment-zero packet detecting every nontrivial zeta zero

Two complementary packets exclude at most one real coefficient at each
spectral point. The nontrivial zeros are countable, so a single real linear
combination avoids vanishing at every zero and every reflected evaluation.
Consequently every coefficient of its actual zero translation kernel is
nonzero. This construction asserts no bound or positivity of that kernel.
-/

set_option autoImplicit false
noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace AEGIS.RHDetectingPacketV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11

/-- Excluding the real part of the unique possible bad ratio is sufficient. -/
theorem affine_ne_zero_of_ratio_excluded (A B : ℂ) (a : ℝ)
    (hAB : ¬ (A = 0 ∧ B = 0)) (ha : a ≠ (-A / B).re) :
    A + (a : ℂ) * B ≠ 0 := by
  intro hzero
  have hB : B ≠ 0 := by
    intro hB0
    apply hAB
    exact ⟨by simpa [hB0] using hzero, hB0⟩
  have heq : (a : ℂ) = -A / B := (eq_div_iff hB).2 (by
    linear_combination hzero)
  exact ha (by simpa using congrArg Complex.re heq)

/-- One moment-zero packet detects both Mellin evaluations for every zero. -/
theorem exists_mellin_detecting_moment_zero_packet :
    ∃ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        mellin g.1 rho.1 ≠ 0 ∧ mellin g.1 (1 - conj rho.1) ≠ 0 := by
  obtain ⟨p, q, hp, hq, hpair⟩ :=
    AEGIS.RHWeilTiltComplementarityV1.unconditional_moment_zero_complementary_pair
  let bad₁ : Set ℝ := Set.range (fun rho : RiemannNontrivialZeroIndexV2 =>
    (-mellin p.1 rho.1 / mellin q.1 rho.1).re)
  let bad₂ : Set ℝ := Set.range (fun rho : RiemannNontrivialZeroIndexV2 =>
    (-mellin p.1 (1 - conj rho.1) / mellin q.1 (1 - conj rho.1)).re)
  have hc₁ : bad₁.Countable := Set.countable_range _
  have hc₂ : bad₂.Countable := Set.countable_range _
  have hex : ∃ a : ℝ, a ∉ bad₁ ∪ bad₂ := by
    by_contra h
    push Not at h
    have heq : bad₁ ∪ bad₂ = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hc₁.union hc₂)
  obtain ⟨a, ha⟩ := hex
  let g := addPacket p (scalePacket (a : ℂ) q)
  refine ⟨g, addPacket_preserves_moments_v10 p (scalePacket (a : ℂ) q) hp
    (scalePacket_preserves_moments_v10 (a : ℂ) q hq), ?_⟩
  intro rho
  have hstrip := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hs₀ : 0 < (1 - conj rho.1).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hstrip.2]
  have hs₁ : (1 - conj rho.1).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hstrip.1]
  have hr₁ : a ≠ (-mellin p.1 rho.1 / mellin q.1 rho.1).re := by
    intro heq
    exact ha (Or.inl ⟨rho, heq.symm⟩)
  have hr₂ : a ≠ (-mellin p.1 (1 - conj rho.1) /
      mellin q.1 (1 - conj rho.1)).re := by
    intro heq
    exact ha (Or.inr ⟨rho, heq.symm⟩)
  change mellin (addPacket p (scalePacket (a : ℂ) q)).1 rho.1 ≠ 0 ∧
    mellin (addPacket p (scalePacket (a : ℂ) q)).1 (1 - conj rho.1) ≠ 0
  rw [mellin_addPacket_v11, mellin_scalePacket_v11,
    mellin_addPacket_v11, mellin_scalePacket_v11]
  exact ⟨affine_ne_zero_of_ratio_excluded _ _ a
    (hpair rho.1 hstrip.1 hstrip.2) hr₁,
    affine_ne_zero_of_ratio_excluded _ _ a
      (hpair (1 - conj rho.1) hs₀ hs₁) hr₂⟩

/-- A single genuine moment-zero packet has every actual zero-kernel
coefficient nonzero. -/
theorem exists_detecting_moment_zero_packet :
    ∃ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g ∧
      ∀ rho : RiemannNontrivialZeroIndexV2, WeilZeroCoefficientV11 g rho ≠ 0 := by
  obtain ⟨g, hm, hg⟩ := exists_mellin_detecting_moment_zero_packet
  refine ⟨g, hm, fun rho => ?_⟩
  unfold WeilZeroCoefficientV11
  rw [autocorrelation_zero_summand_factorization_v11]
  have hmult : (analyticOrderNatAt riemannZeta rho.1 : ℂ) ≠ 0 := by
    exact_mod_cast zeta_analyticOrderNatAt_ne_zero_v11 rho
  exact mul_ne_zero hmult (mul_ne_zero (hg rho).1 ((map_ne_zero conj).mpr (hg rho).2))

#print axioms AEGIS.RHDetectingPacketV1.affine_ne_zero_of_ratio_excluded
#print axioms AEGIS.RHDetectingPacketV1.exists_mellin_detecting_moment_zero_packet
#print axioms AEGIS.RHDetectingPacketV1.exists_detecting_moment_zero_packet

end AEGIS.RHDetectingPacketV1
