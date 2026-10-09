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

import WeilZeroTranslationV11
import WeilMixedAlgebraV2
import WeilAutocorrelationClosureV1
import Mathlib.Tactic

/-!
Fork-local compatibility overlay.

Authoritative AEGIS source anchor:
  Aegis-Omega/AEGIS-OMEGA@589adf0480bd4d7c12c9828027ea6228398377f4

This file preserves the theorem statements from that source and contains only
Lean 4.33.1 / Mathlib 0df444a3 elaboration repairs. It is intentionally kept
in the Formal Conjectures fork; the AEGIS anchor is treated as read-only.
-/


/-!
AEGIS Ω — zero-side two-point translation kernel V11.

For a compact-smooth packet g define the canonical zero quadratic coefficient

  a_rho = m_rho M(g)(rho) conj(M(g)(1-conj rho))

and the translated zero kernel

  K_g(t) = sum_rho a_rho exp((rho-1/2)t).

The strict critical strip gives a uniform bound on the exponential factor for
each fixed real t, so this series is absolutely summable from the already
proved autocorrelation zero summability.

For the exact repository two-point packet

  g + c T_t g

this module proves

  Q(g + c T_t g)
    = (1 + c conj c) Q(g)
      + c K_g(t) + conj c K_g(-t).

This is the exact zero-side two-point identity used by the restricted Weil
criterion.  No positivity or RH conclusion is asserted here.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilZeroTwoPointV11

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedAlgebraV2

/-- Mellin transform is linear under the repository packet scaling. -/
theorem mellin_scalePacket_v11
    (c : ℂ) (g : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (scalePacket c g).1 s = c * mellin g.1 s := by
  change mellin (fun x : ℝ => c * g.1 x) s = _
  have h := mellin_const_smul g.1 s c
  simpa only [smul_eq_mul] using h

/-- Mellin transform is linear under repository packet addition. -/
theorem mellin_addPacket_v11
    (g h : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (addPacket g h).1 s =
      mellin g.1 s + mellin h.1 s := by
  have hg := weil_compact_smooth_mellin_convergent_all_v1 g s
  have hh := weil_compact_smooth_mellin_convergent_all_v1 h s
  have ha := hasMellin_add hg hh
  change mellin (fun x : ℝ => g.1 x + h.1 x) s = _
  exact ha.2

/-- Exact two-point translated packet. -/
def WeilTwoPointTranslateV11
    (g : WeilCompactSmoothGV1) (d : ℝ) (c : ℂ) :
    WeilCompactSmoothGV1 :=
  addPacket g (scalePacket c (translatePacket g d))

/-- Mellin transform of the exact two-point packet. -/
theorem mellin_twoPointTranslate_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) (c s : ℂ) :
    mellin (WeilTwoPointTranslateV11 g d c).1 s =
      (1 + c *
        Complex.exp ((s - (1 / 2 : ℂ)) * (d : ℂ))) *
        mellin g.1 s := by
  unfold WeilTwoPointTranslateV11
  rw [mellin_addPacket_v11, mellin_scalePacket_v11,
    mellin_translatePacket_v11]
  ring

/-- Pointwise coefficient of the canonical zero quadratic. -/
def WeilZeroCoefficientV11
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho

/-- Spectral translation factor. -/
def WeilZeroTranslationFactorV11
    (rho : RiemannNontrivialZeroIndexV2) (d : ℝ) : ℂ :=
  Complex.exp ((rho.1 - (1 / 2 : ℂ)) * (d : ℂ))

/-- The translated zero-kernel family is absolutely summable for every fixed
real translation. -/
theorem zero_translation_kernel_summable_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
      WeilZeroCoefficientV11 g rho *
        WeilZeroTranslationFactorV11 rho d) := by
  have hbase :
      Summable
        (fun rho : RiemannNontrivialZeroIndexV2 =>
          ‖WeilZeroCoefficientV11 g rho‖) := by
    change Summable
      (fun rho : RiemannNontrivialZeroIndexV2 =>
        ‖WeilZeroIndexSummandV1
          (WeilAutocorrelationCompactSmoothV1 g).1 rho‖)
    exact
      weil_compact_smooth_zero_norm_summable_v1
        (WeilAutocorrelationCompactSmoothV1 g)

  let C : ℝ := Real.exp (|d| / 2)
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hmajor := hbase.mul_left C

  apply Summable.of_norm_bounded hmajor
  intro rho
  rw [norm_mul]
  have hs :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  have hre_real :
      (rho.1.re - (1 / 2 : ℝ)) * d ≤ |d| / 2 := by
    have habs : |rho.1.re - 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    calc
      (rho.1.re - 1 / 2) * d
        ≤ |rho.1.re - 1 / 2| * |d| := by
            exact le_trans (le_abs_self _)
              (by rw [abs_mul])
      _ ≤ (1 / 2 : ℝ) * |d| := by
            gcongr
      _ = |d| / 2 := by ring
  have hre :
      (((rho.1 - (1 / 2 : ℂ)) * (d : ℂ))).re ≤
        |d| / 2 := by
    simpa [Complex.mul_re, Complex.sub_re] using hre_real
  have hfactor :
      ‖WeilZeroTranslationFactorV11 rho d‖ ≤ C := by
    unfold WeilZeroTranslationFactorV11 C
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hre
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hfactor
      (norm_nonneg (WeilZeroCoefficientV11 g rho))

/-- Canonical translated zero kernel. -/
def WeilZeroTranslationKernelV11
    (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ∑' rho : RiemannNontrivialZeroIndexV2,
    WeilZeroCoefficientV11 g rho *
      WeilZeroTranslationFactorV11 rho d

/-- Reflected spectral factor appearing after conjugating the second Mellin
factor. -/
private theorem reflected_translation_factor_v11
    (rho : RiemannNontrivialZeroIndexV2) (d : ℝ) :
    conj
      (Complex.exp
        (((1 - conj rho.1) - (1 / 2 : ℂ)) * (d : ℂ))) =
      WeilZeroTranslationFactorV11 rho (-d) := by
  unfold WeilZeroTranslationFactorV11
  rw [← Complex.exp_conj]
  congr 1
  simp [map_neg, map_add, map_mul, map_ofNat, Complex.conj_ofReal]
  ring

/-- Per-zero two-point expansion. -/
theorem twoPoint_zero_summand_expansion_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) (c : ℂ)
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroCoefficientV11 (WeilTwoPointTranslateV11 g d c) rho =
      (1 + c * conj c) * WeilZeroCoefficientV11 g rho +
      c * (WeilZeroCoefficientV11 g rho *
        WeilZeroTranslationFactorV11 rho d) +
      conj c * (WeilZeroCoefficientV11 g rho *
        WeilZeroTranslationFactorV11 rho (-d)) := by
  unfold WeilZeroCoefficientV11
  rw [autocorrelation_zero_summand_factorization_v11,
    autocorrelation_zero_summand_factorization_v11,
    mellin_twoPointTranslate_v11,
    mellin_twoPointTranslate_v11,
    map_mul, map_add, map_one, map_mul,
    reflected_translation_factor_v11]
  simp only [WeilZeroTranslationFactorV11]
  ring_nf
  have hcancel :
      Complex.exp
          (rho.1 * (d : ℂ) + (d : ℂ) * (-1 / 2 : ℂ)) *
        Complex.exp
          (rho.1 * ((-d : ℝ) : ℂ) +
            ((-d : ℝ) : ℂ) * (-1 / 2 : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have hz :
        (rho.1 * (d : ℂ) + (d : ℂ) * (-1 / 2 : ℂ)) +
          (rho.1 * ((-d : ℝ) : ℂ) +
            ((-d : ℝ) : ℂ) * (-1 / 2 : ℂ)) = 0 := by
      push_cast
      ring
    rw [hz, Complex.exp_zero]
  linear_combination
    ((analyticOrderNatAt riemannZeta rho.1 : ℂ) *
      c * conj c * mellin g.1 rho.1 *
      conj (mellin g.1 (1 - conj rho.1))) * hcancel

/-- Canonical zero quadratic of a two-point translated packet. -/
theorem twoPoint_zero_quadratic_expansion_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) (c : ℂ) :
    WeilAutocorrelationZeroQuadraticV11
        (WeilTwoPointTranslateV11 g d c) =
      (1 + c * conj c) *
        WeilAutocorrelationZeroQuadraticV11 g +
      c * WeilZeroTranslationKernelV11 g d +
      conj c * WeilZeroTranslationKernelV11 g (-d) := by
  have hbase :
      Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
        WeilZeroCoefficientV11 g rho) := by
    change Summable
      (WeilZeroIndexSummandV1
        (WeilAutocorrelationCompactSmoothV1 g).1)
    exact
      weil_compact_smooth_zero_summable_v1
        (WeilAutocorrelationCompactSmoothV1 g)
  have hd := zero_translation_kernel_summable_v11 g d
  have hnd := zero_translation_kernel_summable_v11 g (-d)

  unfold WeilAutocorrelationZeroQuadraticV11
  change
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroCoefficientV11
        (WeilTwoPointTranslateV11 g d c) rho) = _

  calc
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroCoefficientV11
        (WeilTwoPointTranslateV11 g d c) rho)
      =
    ∑' rho : RiemannNontrivialZeroIndexV2,
      ((1 + c * conj c) * WeilZeroCoefficientV11 g rho +
       c * (WeilZeroCoefficientV11 g rho *
          WeilZeroTranslationFactorV11 rho d) +
       conj c * (WeilZeroCoefficientV11 g rho *
          WeilZeroTranslationFactorV11 rho (-d))) := by
        apply tsum_congr
        intro rho
        exact twoPoint_zero_summand_expansion_v11 g d c rho
    _ =
      (1 + c * conj c) *
          (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroCoefficientV11 g rho) +
        c * (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroCoefficientV11 g rho *
            WeilZeroTranslationFactorV11 rho d) +
        conj c * (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroCoefficientV11 g rho *
            WeilZeroTranslationFactorV11 rho (-d)) := by
        rw [← hbase.tsum_mul_left,
          ← hd.tsum_mul_left,
          ← hnd.tsum_mul_left]
        have h1 := hbase.mul_left (1 + c * conj c)
        have h2 := hd.mul_left c
        have h3 := hnd.mul_left (conj c)
        rw [← h1.tsum_add h2, ← (h1.add h2).tsum_add h3]
    _ = _ := by
      rfl

end AEGIS.WeilZeroTwoPointV11

#print axioms AEGIS.WeilZeroTwoPointV11.mellin_twoPointTranslate_v11
#print axioms AEGIS.WeilZeroTwoPointV11.zero_translation_kernel_summable_v11
#print axioms AEGIS.WeilZeroTwoPointV11.twoPoint_zero_summand_expansion_v11
#print axioms AEGIS.WeilZeroTwoPointV11.twoPoint_zero_quadratic_expansion_v11
