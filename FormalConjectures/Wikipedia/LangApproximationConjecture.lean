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
# Lang's Logarithmic Diophantine Approximation Conjecture

Klaus Roth proved in 1955 that for every irrational real algebraic number $\alpha$ and every
$\varepsilon > 0$, the inequality $|\alpha - p / q| < q^{-2 - \varepsilon}$ admits only finitely
many coprime integer solutions $(p, q)$ (see also `Constant7a.irrationalityExponent_of_algebraic`
in `FormalConjectures.OptimizationConstants.7a`). Motivated by Khinchin's metric approximation
theorem, Serge Lang conjectured in 1965 (and in his 1966 monograph) that the factor
$q^{-\varepsilon}$ in Roth's bound can be sharpened to $(\log q)^{-1 - \varepsilon}$: for every
irrational real algebraic $\alpha$ and every $\varepsilon > 0$, only finitely many integer pairs
$(p, q)$ with $q \ge 2$ satisfy
$$|\alpha - p / q| < \frac{1}{q^2 (\log q)^{1 + \varepsilon}}.$$

*References:*
- [Wikipedia: Roth's theorem](https://en.wikipedia.org/wiki/Roth%27s_theorem)
- K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika **2** (1955), 1–20.
- S. Lang, *Report on Diophantine approximations*, Bull. Soc. Math. France **93** (1965), 177–192.
- S. Lang, *Introduction to Diophantine Approximations*, Addison-Wesley, Reading, Mass., 1966.
-/

@[expose] public section

namespace LangApproximationConjecture

/-- Predicate asserting that $(p, q) \in \mathbb{Z} \times \mathbb{N}$ with $q \ge 2$ satisfies
Lang's inequality $|\alpha - p / q| < \frac{1}{q^2 (\log q)^{1 + \varepsilon}}$. -/
def IsGoodLogApproximation (α ε : ℝ) (pq : ℤ × ℕ) : Prop :=
  2 ≤ pq.2 ∧
    |α - (pq.1 : ℝ) / (pq.2 : ℝ)| <
      1 / ((pq.2 : ℝ) ^ 2 * (Real.log (pq.2 : ℝ)) ^ (1 + ε))

/-- At $\alpha = 0$ and $\varepsilon = 1$, $(0, 2)$ satisfies `IsGoodLogApproximation`. -/
@[category test, AMS 11]
theorem isGoodLogApproximation_zero_two :
    IsGoodLogApproximation 0 1 (0, 2) := by
  refine ⟨le_rfl, ?_⟩
  simp only [Int.cast_zero, Nat.cast_ofNat, zero_div, sub_zero, abs_zero]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- At $\alpha = 0$ and $\varepsilon = 1$, $(3, 2)$ fails `IsGoodLogApproximation` since
$|0 - 3 / 2| = 3 / 2 > 1 \ge \frac{1}{4 (\log 2)^2}$. -/
@[category test, AMS 11]
theorem not_isGoodLogApproximation_three_two :
    ¬ IsGoodLogApproximation 0 1 (3, 2) := by
  rintro ⟨_, hlt⟩
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h1 := Real.add_one_le_exp (-Real.log 2)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h1
    linarith
  have hpow : ((1 : ℝ) / 2) ^ 2 ≤ (Real.log 2) ^ (1 + (1 : ℝ)) := by
    rw [show (1 : ℝ) + 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hden : (1 : ℝ) ≤ (2 : ℝ) ^ 2 * (Real.log 2) ^ (1 + (1 : ℝ)) := by
    calc (1 : ℝ) = 4 * ((1 : ℝ) / 2) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ 2 * (Real.log 2) ^ (1 + (1 : ℝ)) := by
        have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
        rw [h4]
        linarith [hpow]
  have hbound : 1 / ((2 : ℝ) ^ 2 * (Real.log 2) ^ (1 + (1 : ℝ))) ≤ 1 :=
    div_le_one_of_le₀ hden (by positivity)
  simp only [Int.cast_ofNat, Nat.cast_ofNat, zero_sub, abs_neg] at hlt
  rw [abs_of_pos (by norm_num)] at hlt
  linarith

/-- Any rational number $r \in \mathbb{Q}$ admits infinitely many pairs $(p, q)$ satisfying
`IsGoodLogApproximation r ε`, showing that the `Irrational α` hypothesis in Lang's conjecture is
necessary. -/
@[category API, AMS 11]
theorem infinite_isGoodLogApproximation_ratCast (r : ℚ) (ε : ℝ) :
    {pq : ℤ × ℕ | IsGoodLogApproximation (r : ℝ) ε pq}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (r.num * ((k + 2 : ℕ) : ℤ), r.den * (k + 2)))
    (fun k₁ k₂ h => by
      have h2 : r.den * (k₁ + 2) = r.den * (k₂ + 2) := congrArg Prod.snd h
      have hden : 0 < r.den := r.pos
      exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hden h2))
    fun k => ?_
  have hden : 1 ≤ r.den := r.pos
  have hq2 : 2 ≤ r.den * (k + 2) := by nlinarith
  refine ⟨hq2, ?_⟩
  have hqpos : (0 : ℝ) < ((r.den * (k + 2) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < r.den * (k + 2))
  have hlog : 0 < Real.log ((r.den * (k + 2) : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < r.den * (k + 2)))
  have heq : ((r.num * ((k + 2 : ℕ) : ℤ) : ℤ) : ℝ) / ((r.den * (k + 2) : ℕ) : ℝ) = (r : ℝ) := by
    have hk0 : (k : ℝ) + 2 ≠ 0 := by positivity
    rw [Rat.cast_def]
    push_cast
    exact mul_div_mul_right (r.num : ℝ) (r.den : ℝ) hk0
  dsimp only [Set.mem_ofPred_eq]
  rw [heq, sub_self, abs_zero]
  exact div_pos one_pos (mul_pos (sq_pos_of_pos hqpos) (Real.rpow_pos_of_pos hlog (1 + ε)))

/--
**Roth's Theorem** (1955): for every irrational real algebraic number $\alpha$ and every
$\varepsilon > 0$, only finitely many coprime pairs $(p, q) \in \mathbb{Z} \times \mathbb{N}$ with
$q \ge 1$ satisfy $|\alpha - p / q| < q^{-2 - \varepsilon}$ (compare
`Constant7a.irrationalityExponent_of_algebraic`).
-/
@[category research solved, AMS 11]
theorem roth_rational_approximation_theorem (α : ℝ) (hirr : Irrational α)
    (halg : IsAlgebraic ℚ α) (ε : ℝ) (hε : 0 < ε) :
    {pq : ℤ × ℕ | 1 ≤ pq.2 ∧ pq.1.natAbs.Coprime pq.2 ∧
      |α - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (pq.2 : ℝ) ^ (2 + ε)}.Finite := by
  sorry

/--
**Lang's Logarithmic Diophantine Approximation Conjecture** (1965): for every irrational real
algebraic number $\alpha$ and every $\varepsilon > 0$, only finitely many pairs
$(p, q) \in \mathbb{Z} \times \mathbb{N}$ with $q \ge 2$ (excluding $q \le 1$ so $\log q > 0$; for
irrational $\alpha$, finiteness over all such pairs is equivalent to finiteness over coprime pairs)
satisfy $|\alpha - p / q| < \frac{1}{q^2 (\log q)^{1 + \varepsilon}}$.
-/
@[category research open, AMS 11]
theorem lang_logarithmic_approximation_conjecture (α : ℝ) (hirr : Irrational α)
    (halg : IsAlgebraic ℚ α) (ε : ℝ) (hε : 0 < ε) :
    {pq : ℤ × ℕ | IsGoodLogApproximation α ε pq}.Finite := by
  sorry

end LangApproximationConjecture
