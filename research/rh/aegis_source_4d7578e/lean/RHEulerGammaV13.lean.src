import Mathlib

/-!
AEGIS Ω — a sharp enclosure of Euler's constant, V13.

`0.5752 < γ < 0.5792`. Mathlib's stated `1/2 < γ < 2/3` is too coarse for the margins `0.02 … 0.1` of
the Fourier-side (Krein) certificate in `RH_STATUS.md`, where `γ` enters additively through
`Re ψ(1/4 + iξ/2) = −γ + Σ (1/(n+1) − Re 1/(n + 1/4 + iξ/2))`.

Proof: Mathlib's monotone sandwich `H_n − log(n+1) < γ < H_n − log n`, taken at `n = 256`.
- `H₂₅₆` is enclosed as an exact rational sum.
- `log 256 = 8·log 2` is bounded by `Real.log_two_gt_d9` and `Real.log_two_lt_d9`.
- `log 257 ≤ log 256 + 1/256` follows from `log x ≤ x − 1`.

Not RH. AUTHORITY_EFFECT = NONE.
-/

open Real
set_option autoImplicit false

namespace AEGIS.RHEulerGammaV13

set_option maxRecDepth 100000 in
theorem harmonic_256_bounds :
    (6124344 / 1000000 : ℚ) < harmonic 256 ∧ harmonic 256 < (6124345 / 1000000 : ℚ) := by
  constructor <;> simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero] <;> norm_num

theorem log_256 : Real.log 256 = 8 * Real.log 2 := by
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num

/-- `γ < 0.5792`, from `γ < H₂₅₆ − log 256` and `log 2 > 0.6931471803`. -/
theorem gamma_lt : eulerMascheroniConstant < 5792 / 10000 := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  simp only [eulerMascheroniSeq', show (256 : ℕ) ≠ 0 by norm_num, if_false] at h
  have hH : (harmonic 256 : ℝ) < 6124345 / 1000000 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr harmonic_256_bounds.2
    push_cast at h'; exact h'
  have hl : (Real.log ((256 : ℕ) : ℝ)) = 8 * Real.log 2 := by push_cast; exact log_256
  have h2 := Real.log_two_gt_d9
  rw [hl] at h
  norm_num at h2
  linarith

/-- `0.5752 < γ`, from `H₂₅₆ − log 257 < γ` and `log 257 ≤ log 256 + 1/256`. -/
theorem lt_gamma : (5752 / 10000 : ℝ) < eulerMascheroniConstant := by
  have h := eulerMascheroniSeq_lt_eulerMascheroniConstant 256
  unfold eulerMascheroniSeq at h
  have hH : (6124344 / 1000000 : ℝ) < (harmonic 256 : ℝ) := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr harmonic_256_bounds.1
    push_cast at h'; exact h'
  rw [show ((256 : ℕ) : ℝ) + 1 = 257 by norm_num] at h
  have h257 : Real.log 257 ≤ 8 * Real.log 2 + 1 / 256 := by
    have hq : Real.log ((257 : ℝ) / 256) ≤ (257 : ℝ) / 256 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), log_256] at hq
    linarith
  have h2 := Real.log_two_lt_d9
  norm_num at h2
  linarith

end AEGIS.RHEulerGammaV13

#print axioms AEGIS.RHEulerGammaV13.gamma_lt
#print axioms AEGIS.RHEulerGammaV13.lt_gamma
