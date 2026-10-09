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

import RHKreinFactorV13
import WeilCriterionCompactSmoothV1

/-!
# Exact local decomposition through the Krein factor

Splitting a smooth compactly supported Krein factor preserves both exponential
moments after application of `D² - 1/4`. Binary partitions can be iterated to
produce a finite local decomposition without a residual correction packet.
No sign or bound for cross terms between the resulting atoms is asserted.
-/

open Set MeasureTheory
open scoped ContDiff BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHLocalKreinPartitionV1

open AEGIS.RHKreinFactorV13

/-- The differential factor in `RHKreinFactorV13.moment_zero_parametrization`. -/
def kreinAtom (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv (deriv φ) x - (1 / 4 : ℂ) * φ x

private theorem contDiff_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2

/-- Applying the Krein differential factor preserves smoothness. -/
theorem kreinAtom_contDiff (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (kreinAtom φ) :=
  (contDiff_deriv (contDiff_deriv hφ)).sub (contDiff_const.mul hφ)

/-- The differential factor does not enlarge topological support. -/
theorem kreinAtom_support (φ : ℝ → ℂ) : tsupport (kreinAtom φ) ⊆ tsupport φ := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hnot
  have h0 := image_eq_zero_of_notMem_tsupport hnot
  have hnotD : x ∉ tsupport (deriv φ) := fun h => hnot (tsupport_deriv_subset h)
  have h2 := deriv_of_notMem_tsupport hnotD
  exact hx (by simp [kreinAtom, h0, h2])

private theorem integral_deriv_zero {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) : (∫ x : ℝ, deriv F x) = 0 := by
  have hint : Integrable (deriv F) :=
    (hF.continuous_deriv le_rfl).integrable_of_hasCompactSupport hFc.deriv
  have h := intervalIntegral.integral_Iic_add_Ioi (f := deriv F) (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn
  rw [HasCompactSupport.integral_Iic_deriv_eq hF hFc 0,
    HasCompactSupport.integral_Ioi_deriv_eq hF hFc 0] at h
  simpa using h.symm

/-- The two exponential weights annihilate each smooth compact Krein atom. -/
theorem kreinAtom_exponential_moment (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (c : ℝ) (hc2 : c * c = 1 / 4) :
    (∫ x : ℝ, ex c x * kreinAtom φ x) = 0 := by
  let F : ℝ → ℂ := fun x => ex c x * (deriv φ x - (c : ℂ) * φ x)
  have hD := contDiff_deriv hφ
  have hF : ContDiff ℝ 1 F := by
    exact ((contDiff_ex c).mul (hD.sub (contDiff_const.mul hφ))).of_le (by simp)
  have hFc : HasCompactSupport F := (hc.deriv.sub hc.mul_left).mul_left
  have hcc : (c : ℂ) * (c : ℂ) = (1 / 4 : ℂ) := by
    rw [← Complex.ofReal_mul, hc2]
    norm_num
  have hder : deriv F = fun x => ex c x * kreinAtom φ x := by
    funext x
    have h1 := (hφ.differentiable (by simp) x).hasDerivAt
    have h2 := (hD.differentiable (by simp) x).hasDerivAt
    have hd := (hasDerivAt_ex c x).mul (h2.sub (h1.const_mul (c : ℂ)))
    have hd' : HasDerivAt F (ex c x * kreinAtom φ x) x := by
      apply hd.congr_deriv
      calc
        (c : ℂ) * ex c x * (deriv φ x - (c : ℂ) * φ x) +
            ex c x * (deriv (deriv φ) x - (c : ℂ) * deriv φ x) =
            ex c x * (deriv (deriv φ) x - ((c : ℂ) * (c : ℂ)) * φ x) := by ring
        _ = ex c x * kreinAtom φ x := by rw [hcc]; rfl
    exact hd'.deriv
  rw [← hder]
  exact integral_deriv_zero hF hFc

/-- Both moments use the exact signs and normalization of the source factor. -/
theorem kreinAtom_moments (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    (∫ x : ℝ, (Real.exp (-x / 2) : ℂ) * kreinAtom φ x) = 0 ∧
      (∫ x : ℝ, (Real.exp (x / 2) : ℂ) * kreinAtom φ x) = 0 := by
  have hm := kreinAtom_exponential_moment φ hφ hc (-1 / 2) (by norm_num)
  have hp := kreinAtom_exponential_moment φ hφ hc (1 / 2) (by norm_num)
  constructor
  · simpa only [ex, show ∀ x : ℝ, (-1 / 2 : ℝ) * x = -x / 2 by intro x; ring] using hm
  · simpa only [ex, show ∀ x : ℝ, (1 / 2 : ℝ) * x = x / 2 by intro x; ring] using hp

/-- The differential factor is additive on smooth functions. -/
theorem kreinAtom_add (φ ψ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) :
    kreinAtom (fun x => φ x + ψ x) = fun x => kreinAtom φ x + kreinAtom ψ x := by
  have hfirst : deriv (fun x => φ x + ψ x) = fun x => deriv φ x + deriv ψ x := by
    funext x
    exact ((hφ.differentiable (by simp) x).hasDerivAt.add
      (hψ.differentiable (by simp) x).hasDerivAt).deriv
  have hsecond : deriv (fun x => deriv φ x + deriv ψ x) =
      fun x => deriv (deriv φ) x + deriv (deriv ψ) x := by
    funext x
    exact (((contDiff_deriv hφ).differentiable (by simp) x).hasDerivAt.add
      ((contDiff_deriv hψ).differentiable (by simp) x).hasDerivAt).deriv
  funext x
  simp only [kreinAtom, hfirst, hsecond]
  ring

/-- The exact derivative terms created by a local cutoff. -/
theorem kreinAtom_mul (χ φ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hφ : ContDiff ℝ ∞ φ) (x : ℝ) :
    kreinAtom (fun y => χ y * φ y) x =
      χ x * kreinAtom φ x + 2 * deriv χ x * deriv φ x + deriv (deriv χ) x * φ x := by
  have hfirst : deriv (fun y => χ y * φ y) =
      fun y => deriv χ y * φ y + χ y * deriv φ y := by
    funext y
    exact ((hχ.differentiable (by simp) y).hasDerivAt.mul
      (hφ.differentiable (by simp) y).hasDerivAt).deriv
  have hχ1 := (hχ.differentiable (by simp) x).hasDerivAt
  have hφ1 := (hφ.differentiable (by simp) x).hasDerivAt
  have hχ2 := ((contDiff_deriv hχ).differentiable (by simp) x).hasDerivAt
  have hφ2 := ((contDiff_deriv hφ).differentiable (by simp) x).hasDerivAt
  have hsecond := (hχ2.mul hφ1).add (hχ1.mul hφ2)
  change HasDerivAt (fun y => deriv χ y * φ y + χ y * deriv φ y) _ x at hsecond
  simp only [kreinAtom, hfirst, hsecond.deriv]
  ring

/-- Splitting the factor gives exact reconstruction, with no correction carry. -/
theorem kreinAtom_partition_two (φ χ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) :
    (fun x => kreinAtom (fun y => χ y * φ y) x +
      kreinAtom (fun y => (1 - χ y) * φ y) x) = kreinAtom φ := by
  rw [← kreinAtom_add _ _ (hχ.mul hφ) ((contDiff_const.sub hχ).mul hφ)]
  congr 1
  funext x
  ring

/-- Each factor in an arbitrary smooth binary partition has both zero moments. -/
theorem kreinAtom_partition_moments (φ χ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport φ) :
    ((∫ x : ℝ, (Real.exp (-x / 2) : ℂ) * kreinAtom (fun y => χ y * φ y) x) = 0 ∧
      (∫ x : ℝ, (Real.exp (x / 2) : ℂ) * kreinAtom (fun y => χ y * φ y) x) = 0) ∧
    ((∫ x : ℝ, (Real.exp (-x / 2) : ℂ) *
      kreinAtom (fun y => (1 - χ y) * φ y) x) = 0 ∧
      (∫ x : ℝ, (Real.exp (x / 2) : ℂ) *
        kreinAtom (fun y => (1 - χ y) * φ y) x) = 0) :=
  ⟨kreinAtom_moments _ (hχ.mul hφ) hc.mul_left,
    kreinAtom_moments _ ((contDiff_const.sub hχ).mul hφ) hc.mul_left⟩

/-- Finite smooth sums commute with the Krein differential factor. -/
theorem kreinAtom_finset_sum {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ContDiff ℝ ∞ (fun x => ∑ i ∈ s, φ i x) ∧
      kreinAtom (fun x => ∑ i ∈ s, φ i x) = fun x => ∑ i ∈ s, kreinAtom (φ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · simpa only [Finset.sum_empty] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)))
    · funext x
      simp [kreinAtom]
  | @insert a s ha ih =>
    constructor
    · simpa only [Finset.sum_insert ha] using (hφ a).add ih.1
    · simp only [Finset.sum_insert ha]
      rw [kreinAtom_add _ _ (hφ a) ih.1, ih.2]

/-- A finite smooth partition on the factor's support reconstructs the exact atom. -/
theorem kreinAtom_finite_partition {ι : Type*} (s : Finset ι)
    (φ : ℝ → ℂ) (χ : ι → ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x, φ x ≠ 0 → ∑ i ∈ s, χ i x = 1) :
    kreinAtom φ = fun x => ∑ i ∈ s, kreinAtom (fun y => χ i y * φ y) x := by
  have heq : (fun x => ∑ i ∈ s, χ i x * φ x) = φ := by
    funext x
    rw [← Finset.sum_mul]
    by_cases hx : φ x = 0
    · simp [hx]
    · rw [hpart x hx, one_mul]
  simpa only [heq] using
    (kreinAtom_finset_sum s (fun i x => χ i x * φ x) (fun i => (hχ i).mul hφ)).2

/-- The actual packet moments supply the compact factor to which the partitions apply. -/
theorem actual_packet_has_compact_krein_factor (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) (a b : ℝ) (hab : a ≤ b)
    (hs : tsupport (lift g.1) ⊆ Icc a b) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ lift g.1 = kreinAtom φ := by
  have hG : ContDiff ℝ ∞ (lift g.1) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.div_const 2).exp).mul
      (g.2.1.comp Real.contDiff_exp)
  have hminus : (∫ x : ℝ, (Real.exp (-x / 2) : ℂ) * lift g.1 x) = 0 := by
    rw [lift_moment_minus]
    exact hm.1
  have hplus : (∫ x : ℝ, (Real.exp (x / 2) : ℂ) * lift g.1 x) = 0 := by
    rw [lift_moment_plus]
    exact hm.2
  obtain ⟨φ, hφ, hsφ, heq⟩ :=
    moment_zero_parametrization (lift g.1) a b hab hG hs hminus hplus
  refine ⟨φ, hφ, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ, ?_⟩
  exact funext heq

#print axioms AEGIS.RHLocalKreinPartitionV1.kreinAtom_support
#print axioms AEGIS.RHLocalKreinPartitionV1.kreinAtom_moments
#print axioms AEGIS.RHLocalKreinPartitionV1.kreinAtom_mul
#print axioms AEGIS.RHLocalKreinPartitionV1.kreinAtom_partition_two
#print axioms AEGIS.RHLocalKreinPartitionV1.kreinAtom_partition_moments
#print axioms AEGIS.RHLocalKreinPartitionV1.kreinAtom_finite_partition
#print axioms AEGIS.RHLocalKreinPartitionV1.actual_packet_has_compact_krein_factor

end AEGIS.RHLocalKreinPartitionV1
