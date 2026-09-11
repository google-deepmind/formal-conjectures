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

/-!
# Tao's Optimization Constant 7a / The Irrationality Measure of $\pi$

*References:*
- [Tao's Optimization Constant 7a](https://teorth.github.io/optimizationproblems/constants/7a.html)
- [D1842] Dirichlet, L. G. P., *Verallgemeinerung eines Satzes aus der Lehre von den
  Kettenbrüchen nebst einigen Anwendungen auf die Theorie der Zahlen*. Sitzungsberichte der
  Preussischen Akademie der Wissenschaften (1842), 93–95.
- [M1953] Mahler, K., *On the approximation of $\pi$*. Nederl. Akad. Wetensch. Proc. Ser. A
  **56** = Indag. Math. **15** (1953), 30–42.
- [R1955] Roth, K. F., [*Rational approximations to algebraic
  numbers*](https://doi.org/10.1112/S0025579300000644). Mathematika **2** (1955), 1–20.
- [RV1993] Rhin, G. and Viola, C., [*On the irrationality measure of
  $\zeta(2)$*](https://doi.org/10.5802/aif.1322). Ann. Inst. Fourier **43** (1993), 85–109.
- [ZZ2020] Zeilberger, D. and Zudilin, W., *The irrationality measure of $\pi$ is at most
  $7.103205334137\ldots$*. Moscow J. Comb. Number Theory **9** (2020), 407–419.
  [arXiv:1912.06345](https://arxiv.org/abs/1912.06345)
-/

namespace Constant7a

open Real ENNReal Set NNReal

/-- The irrationality exponent of a real number. -/
noncomputable def irrationalityExponent (x : ℝ) : ℝ≥0∞ :=
  sSup ((↑) '' {p : ℝ≥0 | LiouvilleWith p x})

/-- The irrationality exponent of a rational number is one. -/
@[category API, AMS 11]
theorem irrationalityExponent_ratCast (x : ℚ) : irrationalityExponent x = 1 := by
  unfold irrationalityExponent
  apply le_antisymm
  · simp only [sSup_le_iff, mem_image, mem_ofPred_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, coe_le_one_iff]
    intro _ h
    simpa using (LiouvilleWith.irrational h).mt
  · apply le_sSup
    simp only [mem_image, mem_ofPred_eq, ENNReal.coe_eq_one, exists_eq_right, NNReal.coe_one]
    exact liouvilleWith_one x

@[category API, AMS 11]
theorem le_irrationalityExponent_iff (x : ℝ) (y : ℝ≥0∞) :
    y ≤ irrationalityExponent x ↔ ∀ z : ℝ≥0, z < y → LiouvilleWith z x := by
  rw [irrationalityExponent, le_sSup_iff_forall_lt]
  refine ⟨fun h z zy ↦ ?_, fun h z zy ↦ ?_⟩
  · obtain ⟨a, ha, za⟩ := h z zy
    simp only [mem_image, mem_ofPred_eq] at ha
    obtain ⟨r, hr, ra⟩ := ha
    apply LiouvilleWith.mono hr
    simp only [NNReal.coe_le_coe]
    suffices (z : ℝ≥0∞) ≤ r by simpa
    grind
  · simp only [mem_image, mem_ofPred_eq, exists_exists_and_eq_and]
    rcases eq_or_ne y ⊤ with rfl | hy
    · simp_all only [coe_lt_top, forall_const, true_and]
      refine ⟨z.toNNReal + 1, ?_⟩
      rw [coe_add, ENNReal.coe_one, coe_toNNReal zy.ne]
      exact lt_add_right zy.ne one_ne_zero
    obtain ⟨a, za, ay⟩ := DenselyOrdered.dense z y zy
    refine ⟨a.toNNReal, ?_, ?_⟩
    · apply h
      rwa [ENNReal.coe_toNNReal (by grind)]
    · rwa [ENNReal.coe_toNNReal (by grind)]

@[category API, AMS 11]
theorem irrationalityExponent_eq_top_iff (x : ℝ) : irrationalityExponent x = ⊤ ↔ Liouville x := by
  simp_rw [← ENNReal.not_lt_top, not_lt, le_irrationalityExponent_iff, ← forall_liouvilleWith_iff,
    coe_lt_top, forall_const]
  exact ⟨fun h p ↦ (h p.toNNReal).mono <| le_coe_toNNReal p, fun h z ↦ h z⟩

/-- Every irrational real number has irrationality exponent at least two by Dirichlet's
approximation theorem [D1842]. -/
@[category textbook, AMS 11]
theorem two_le_irrationalityExponent {x : ℝ} (hx : Irrational x) :
    2 ≤ irrationalityExponent x := by
  sorry

/-- Every algebraic real number has irrationality exponent at most two. For irrational algebraic
numbers, this is Roth's theorem [R1955]. -/
@[category research solved, AMS 11]
theorem irrationalityExponent_of_algebraic {x : ℝ} (hx : IsAlgebraic ℚ x) :
    irrationalityExponent x ≤ 2 := by
  sorry

/-- **Tao's Optimization Constant 7a / The irrationality measure of $\pi$**. -/
noncomputable def C7a : ℝ≥0∞ := irrationalityExponent π

/-- The first and current best known lower bound, given by Dirichlet's theorem [D1842]. This bound
holds for every irrational real number. -/
@[category textbook, AMS 11]
theorem c7a_lower_bound : 2 ≤ C7a := two_le_irrationalityExponent irrational_pi

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 11]
theorem c7a_lower_bound_improved : answer(sorry) ↔ 2 < C7a := by
  sorry

/-- The first known upper bound, proved by Mahler in [M1953]. This was the first proof that
$C_{7a}$ is finite, or equivalently that $\pi$ is not a Liouville number. -/
@[category research solved, AMS 11]
theorem c7a_le_42 : C7a ≤ 42 := by
  sorry

/-- An intermediate upper bound proved by Rhin and Viola in [RV1993]. It follows from an effective
irrationality measure for $\zeta(2) = \pi^2 / 6$. -/
@[category research solved, AMS 11]
theorem c7a_lt_14_797075 : C7a < 14.797075 := by
  sorry

/-- The current best known upper bound, proved by Zeilberger and Zudilin in [ZZ2020]. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound : C7a < 7.103205334138 := by
  sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 11]
theorem c7a_upper_bound_improved : answer(sorry) ↔ C7a < 7.103205334137 := by
  sorry

end Constant7a
