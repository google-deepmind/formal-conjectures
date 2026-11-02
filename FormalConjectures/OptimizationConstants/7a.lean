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

public import FormalConjecturesUtil

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
- [OAI2026] OpenAI, [*The irrationality exponent of $\pi$ is
  2*](https://github.com/openai/math/blob/main/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf),
  2026.
-/

@[expose] public section

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
@[optimization_constant "7a"]
noncomputable def C7a : ℝ≥0∞ := irrationalityExponent π

/-- The sharp lower bound, given by Dirichlet's theorem [D1842]. This bound
holds for every irrational real number. -/
@[category textbook, AMS 11]
theorem c7a_lower_bound : 2 ≤ C7a := two_le_irrationalityExponent irrational_pi

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

/-- The best upper bound before [OAI2026], proved by Zeilberger and Zudilin in [ZZ2020]. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound : C7a < 7.103205334138 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The irrationality measure of $\pi$ is exactly $2$, proved by OpenAI in [OAI2026]; see
`c7a_eq_two.variants.openai`. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Main.lean#L17"]
theorem c7a_eq_two : C7a = 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The statement of the linked Lean proof [OAI2026]. For every $\nu > 2$, $|\pi - p/q| \ge q^{-\nu}$
for all large $q$. The supremum of the exponents $\nu > 0$ for which infinitely many rationals $r$
satisfy $0 < |\pi - r| < \operatorname{den}(r)^{-\nu}$ is $2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Main.lean#L17"]
theorem c7a_eq_two.variants.openai :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q →
        (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.pi - (r : ℝ)| ∧
        |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  sorry

/-- The linked statement gives `C7a = 2`. -/
@[category test, AMS 11]
theorem c7a_eq_two_of_openai (h : type_of% c7a_eq_two.variants.openai) : C7a = 2 := by
  have hliouville (ν : ℝ) (hν : 0 < ν)
      (hinf : Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |π - (r : ℝ)| ∧ |π - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}) :
      LiouvilleWith ν π := by
    refine ⟨1, Filter.frequently_atTop.2 ?_⟩
    intro N
    -- Bounded denominators and distance less than one give a finite set of rationals.
    let t : Set ℚ := (fun v : ℤ × ℕ => (v.1 : ℚ) / v.2) ''
      (Set.Icc 0 (5 * (N : ℤ)) ×ˢ Set.Icc 0 N)
    have ht : t.Finite := ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).image _
    obtain ⟨r, hr, hrnot⟩ := hinf.exists_notMem_finite ht
    have hnear : |π - (r : ℝ)| < 1 := hr.2.2.trans_le
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hr.1))
        (neg_nonpos.mpr hν.le))
    have hr0 : 0 ≤ (r : ℝ) := by
      have := (abs_lt.mp hnear).2
      have := Real.pi_gt_three
      linarith
    have hr5 : (r : ℝ) ≤ 5 := by
      have := (abs_lt.mp hnear).1
      have := Real.pi_lt_four
      linarith
    have hnum : (r.num : ℝ) = (r : ℝ) * r.den := by
      rw [Rat.cast_def, div_mul_cancel₀ _ (by exact_mod_cast r.den_nz)]
    have hden : N ≤ r.den := by
      by_contra hn
      have hn' : r.den ≤ N := by omega
      apply hrnot
      refine ⟨(r.num, r.den), ⟨?_, ⟨Nat.zero_le _, hn'⟩⟩, ?_⟩
      · constructor
        · have hnonneg : (0 : ℝ) ≤ r.num := by
            rw [hnum]
            exact mul_nonneg hr0 (Nat.cast_nonneg _)
          exact_mod_cast hnonneg
        · have hbound : (r.num : ℝ) ≤ 5 * (N : ℝ) := by
            rw [hnum]
            exact (mul_le_mul_of_nonneg_right hr5 (Nat.cast_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hn') (by norm_num))
          exact_mod_cast hbound
      · exact Rat.num_div_den r
    refine ⟨r.den, hden, r.num, ?_, ?_⟩
    · simpa only [Rat.cast_def] using (sub_ne_zero.mp (abs_pos.mp hr.2.1))
    · simpa only [Rat.cast_def, Real.rpow_neg (Nat.cast_nonneg _), one_div] using hr.2.2
  apply le_antisymm
  · unfold C7a irrationalityExponent
    apply sSup_le
    rintro _ ⟨p, hp, rfl⟩
    suffices (p : ℝ) ≤ 2 by exact_mod_cast this
    by_contra! hp2
    obtain ⟨ν, hν2, hνp⟩ := exists_between hp2
    obtain ⟨Q, hQ2, hQ⟩ := h.1 ν hν2
    obtain ⟨q, hq, m, _, hm⟩ :=
      ((Filter.eventually_ge_atTop Q.toNat).and_frequently
        (hp.frequently_lt_rpow_neg hνp)).exists
    have hqQ : Q ≤ (q : ℤ) := by
      have hq' : (Q.toNat : ℤ) ≤ q := by exact_mod_cast hq
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ Q)] using hq'
    have hbound := hQ m q hqQ
    exact (not_lt_of_ge (by simpa only [Int.cast_natCast] using hbound)) hm
  · apply (le_irrationalityExponent_iff π 2).2
    intro z hz
    let S : Set ℝ := {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |π - (r : ℝ)| ∧ |π - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}}
    have hsup : sSup S = 2 := h.2
    have hne : S.Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty.mp he, Real.sSup_empty] at hsup
      norm_num at hsup
    have hb : BddAbove S := by
      by_contra hb
      rw [Real.sSup_of_not_bddAbove hb] at hsup
      norm_num at hsup
    have hz' : (z : ℝ) < sSup S := by
      rw [hsup]
      exact_mod_cast hz
    obtain ⟨ν, hν, hzν⟩ := (lt_csSup_iff hb hne).mp hz'
    exact (hliouville ν hν.1 hν.2).mono hzν.le

end Constant7a
