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
# Gieseking's Constant

*Gieseking's constant* $V = \operatorname{Cl}_2(\pi / 3) \approx 1.0149416064$
([OEIS A143298](https://oeis.org/A143298)) measures the hyperbolic volume attached to Gieseking's
cusped $3$-manifold. Via the nontrivial Dirichlet character $\chi_{-3}$ modulo $3$
[Fi03, pp. 232–233], it satisfies
$$V = \frac{3\sqrt{3}}{4} L(2, \chi_{-3})
  = \frac{3\sqrt{3}}{4} \sum_{k=0}^{\infty}
      \left(\frac{1}{(3k + 1)^2} - \frac{1}{(3k + 2)^2}\right).$$
Calegari, Dimitrov, and Tang [CDT24] proved that $1, \pi^2, L(2, \chi_{-3})$ are
$\mathbb{Q}$-linearly independent, establishing that $\sqrt{3} V$ is irrational, whereas
irrationality of $V$ itself remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Gieseking_manifold#Gieseking_constant)
- [OEIS A143298](https://oeis.org/A143298)
- [Fi03] S. R. Finch, *Mathematical Constants*, Cambridge Univ. Press, 2003, pp. 232–233.
- [CDT24] F. Calegari, V. Dimitrov, and Y. Tang, *The linear independence of $1$, $\zeta(2)$, and
  $L(2, \chi_{-3})$*, [arXiv:2408.15403](https://arxiv.org/abs/2408.15403) (2024).
-/

@[expose] public section

namespace GiesekingConstant

/-- Paired Dirichlet summand $(3n + 1)^{-2} - (3n + 2)^{-2}$ in $L(2, \chi_{-3})$. -/
noncomputable def giesekingTerm (n : ℕ) : ℝ :=
  1 / (3 * (n : ℝ) + 1) ^ 2 - 1 / (3 * (n : ℝ) + 2) ^ 2

/-- Gieseking's constant $V = \frac{3\sqrt{3}}{4} \sum_{n=0}^\infty ((3n+1)^{-2} - (3n+2)^{-2})$. -/
noncomputable def giesekingConstant : ℝ :=
  (3 * Real.sqrt 3 / 4) * ∑' n : ℕ, giesekingTerm n

/-- At $n = 0$, the initial paired term $1/1^2 - 1/2^2$ equals $3/4$. -/
@[category test, AMS 11 33]
theorem giesekingTerm_zero : giesekingTerm 0 = 3 / 4 := by
  unfold giesekingTerm
  norm_num

/-- Every paired term `giesekingTerm n` is strictly positive. -/
@[category API, AMS 11 33]
theorem giesekingTerm_pos (n : ℕ) : 0 < giesekingTerm n := by
  unfold giesekingTerm
  have hsq : (3 * (n : ℝ) + 1) ^ 2 < (3 * (n : ℝ) + 2) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact sub_pos.mpr (one_div_lt_one_div_of_lt (by positivity) hsq)

/-- The paired series `giesekingTerm` is summable over $\mathbb{N}$. -/
@[category API, AMS 11 33]
theorem summable_giesekingTerm : Summable giesekingTerm := by
  refine Summable.of_nonneg_of_le (fun n => (giesekingTerm_pos n).le) ?_
    ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (fun a b (hab : a + 1 = b + 1) => by omega))
  intro n
  unfold giesekingTerm
  have hle : ((n + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) + 1 := by
    push_cast
    linarith
  have hsq : (((n + 1 : ℕ) : ℝ)) ^ 2 ≤ (3 * (n : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hinv : 1 / (3 * (n : ℝ) + 1) ^ 2 ≤ (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (by positivity) hsq
  have hsub : 1 / (3 * (n : ℝ) + 1) ^ 2 - 1 / (3 * (n : ℝ) + 2) ^ 2 ≤
      1 / (3 * (n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ 1 / (3 * (n : ℝ) + 2) ^ 2 := by positivity
    linarith
  simpa using hsub.trans hinv

/-- Gieseking's constant is strictly positive. -/
@[category API, AMS 11 33]
theorem giesekingConstant_pos : 0 < giesekingConstant := by
  unfold giesekingConstant
  have htsum_pos : 0 < ∑' n : ℕ, giesekingTerm n :=
    Summable.tsum_pos summable_giesekingTerm (fun n => (giesekingTerm_pos n).le) 0
      (giesekingTerm_pos 0)
  exact mul_pos (by positivity) htsum_pos

/-- Gieseking's constant strictly exceeds $1$ (from the $n = 0, 1$ partial sum). -/
@[category test, AMS 11 33]
theorem one_lt_giesekingConstant : 1 < giesekingConstant := by
  unfold giesekingConstant
  have hle : ∑ k ∈ ({0, 1} : Finset ℕ), giesekingTerm k ≤ ∑' n : ℕ, giesekingTerm n :=
    summable_giesekingTerm.sum_le_tsum ({0, 1} : Finset ℕ) (fun k _ => (giesekingTerm_pos k).le)
  have hsum01 : ∑ k ∈ ({0, 1} : Finset ℕ), giesekingTerm k = 309 / 400 := by
    norm_num [giesekingTerm]
  have hsqrt : (1600 / 927 : ℝ) < Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1600 / 927)]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- Scaling by $\sqrt{3}$ gives $\sqrt{3} V = \frac{9}{4} L(2, \chi_{-3})$. -/
@[category API, AMS 11 33]
theorem sqrt_three_mul_giesekingConstant :
    Real.sqrt 3 * giesekingConstant = (9 / 4 : ℝ) * ∑' n : ℕ, giesekingTerm n := by
  unfold giesekingConstant
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 3 * ((3 * Real.sqrt 3 / 4) * ∑' n : ℕ, giesekingTerm n)
      = (3 * (Real.sqrt 3 * Real.sqrt 3) / 4) * ∑' n : ℕ, giesekingTerm n := by ring
    _ = (9 / 4 : ℝ) * ∑' n : ℕ, giesekingTerm n := by rw [hsq]; norm_num

/--
Calegari–Dimitrov–Tang theorem [CDT24]: the real numbers $1$, $\pi^2$, and
$L(2, \chi_{-3}) = \sum_{n=0}^\infty ((3n+1)^{-2} - (3n+2)^{-2})$ are linearly independent over
$\mathbb{Q}$.
-/
@[category research solved, AMS 11 33]
theorem calegari_dimitrov_tang_linearIndependent :
    LinearIndependent ℚ ![1, Real.pi ^ 2, ∑' n : ℕ, giesekingTerm n] := by
  sorry

/--
Corollary of [CDT24]: $\sqrt{3} V = \frac{9}{4} L(2, \chi_{-3})$ is irrational.
-/
@[category research solved, AMS 11 33]
theorem irrational_sqrt_three_mul_giesekingConstant :
    Irrational (Real.sqrt 3 * giesekingConstant) := by
  sorry

/--
Is Gieseking's constant $V = \frac{3\sqrt{3}}{4} L(2, \chi_{-3})$ irrational?
-/
@[category research open, question, AMS 11 33]
theorem gieseking_constant_irrational :
    Irrational giesekingConstant := by
  sorry

end GiesekingConstant
