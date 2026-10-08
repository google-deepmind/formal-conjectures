import RHDyadicDiagonalV13
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic

/-!
AEGIS Ω — unconditional Weil positivity on the whole narrow-support class, V13.

`RHDyadicDiagonalV13.diagonal_lower` has a single hypothesis on the packet:
its log-support lies in an interval of half-width `r ≤ 1/64`.  Nothing there
asks the packet to be a single bump.  Every moment-zero packet of that kind —
in particular every dense combination `Σ zⱼ T_{j·d} g` with `d ≪ r`, and every
smooth function whatever its shape — satisfies

  (103/100) · E(h) ≤ −Re B(h, h) = −Re RHS(Autocorr h),

because the autocorrelation of such an `h` has log-support inside `(−1/32, 1/32)`,
where the only integer is `1` and `Λ(1) = 0`: the prime sum is identically zero
and only the Archimedean term (with its `1/|u|` singularity, positive) and the
pole term remain.  The explicit formula then makes the canonical zero quadratic
nonnegative on the entire class

  { h : WeilCompactSmoothGV1 | moments zero, log-support ⊆ [a − 1/64, a + 1/64] }.

This is an infinite-dimensional class, dense in every function class supported
in such an interval — the "dense spacing" case.  It is not universality: the
open target quantifies over packets of every width, and once the log-support
width reaches `log 2` the prime `2` enters the autocorrelation window.
AUTHORITY_EFFECT = NONE.
-/

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowSupportPositivityV13
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- Arithmetic side nonpositive for every moment-zero packet of half-width `≤ 1/64`
(no hypothesis on the shape of the packet). -/
theorem narrow_arithmetic_nonpositive (h : WeilCompactSmoothGV1) (r a : ℝ)
    (hr0 : 0 < r) (hr : r ≤ 1 / 64) (hw : HalfWidthAt h r a) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 h)).re ≤ 0 := by
  have hw64 : HalfWidthAt h (1 / 64) a := by
    intro t ht
    have := hw ht
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hd := diagonal_lower_recovers_103_over_100 h a hw64
  have hE := energy_nonnegative h.1
  change (B h h).re ≤ 0
  nlinarith

/-- Strict coercivity on the same class. -/
theorem narrow_coercive (h : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt h (1 / 64) a) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 h)).re ≤ -(103 / 100 : ℝ) * energy h.1 := by
  have hd := diagonal_lower_recovers_103_over_100 h a hw
  change (B h h).re ≤ _
  linarith

/-- **Weil positivity of the canonical zero quadratic on the whole narrow-support
class**: every moment-zero packet whose log-support fits in an interval of length
`≤ 1/32`, of any shape. -/
theorem narrow_zero_quadratic_nonnegative (h : WeilCompactSmoothGV1) (r a : ℝ)
    (hr0 : 0 < r) (hr : r ≤ 1 / 64) (hw : HalfWidthAt h r a)
    (hm : WeilMomentConditionsV1 h) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 h) rho).re :=
  (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 h hm).mp
    (narrow_arithmetic_nonpositive h r a hr0 hr hw)

/-- The open target, restricted to the narrow class, is therefore closed. -/
theorem universal_on_narrow_class (a : ℝ) :
    ∀ h : WeilCompactSmoothGV1, HalfWidthAt h (1 / 64) a → WeilMomentConditionsV1 h →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 h) rho).re :=
  fun h hw hm => narrow_zero_quadratic_nonnegative h (1 / 64) a (by norm_num) le_rfl hw hm

end AEGIS.RHNarrowSupportPositivityV13

#print axioms AEGIS.RHNarrowSupportPositivityV13.narrow_coercive
#print axioms AEGIS.RHNarrowSupportPositivityV13.narrow_zero_quadratic_nonnegative
#print axioms AEGIS.RHNarrowSupportPositivityV13.universal_on_narrow_class
