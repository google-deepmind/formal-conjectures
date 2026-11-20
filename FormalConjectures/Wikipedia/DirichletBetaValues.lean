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
# Irrationality and Transcendence of Even Dirichlet Beta Values

For $\operatorname{Re}(s) > 0$, $\beta(s) = \sum_{n=0}^{\infty} (-1)^n / (2n + 1)^s$ denotes the
Dirichlet $L$-series attached to the non-principal character modulo $4$. At positive odd integers,
$\beta(2k + 1)$ is a nonzero rational multiple of $\pi^{2k + 1}$ and hence transcendental. At
positive even exponents, Tanguy Rivoal and Wadim Zudilin [RZ03] proved that infinitely many
$\beta(2k)$ are irrational, and Zudilin [Zu19] proved that at least one among
$\beta(2), \beta(4), \dots, \beta(12)$ is irrational. While irrationality of Catalan's constant
$G = \beta(2)$ has been established (`Irrational.irrational_catalanConstant`), irrationality of any
individual $\beta(2k)$ with $k \ge 2$ and transcendence of every $\beta(2k)$ (see
`Transcendental.transcendental_catalanConstant` for $k = 1$) remain open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Dirichlet_beta_function#Specific_values)
- [RZ03] T. Rivoal and W. Zudilin, *Diophantine properties of numbers related to Catalan's
  constant*, Math. Ann. **326** (2003), no. 4, 705–721.
- [Zu19] W. Zudilin, *Arithmetic of Catalan's constant and its relatives*, Abh. Math. Semin. Univ.
  Hambg. **89** (2019), no. 1, 45–53.
-/

@[expose] public section

namespace DirichletBetaValues

/-- Alternating odd-reciprocal series $\beta(s) = \sum_{n=0}^{\infty} (-1)^n / (2n + 1)^s$ for
integer exponents $s \ge 2$ (where the series converges absolutely; for $s \in \{0, 1\}$, Lean's
`tsum` over `ℝ` returns `0` rather than the analytic values $\beta(0) = 1/2$ and
$\beta(1) = \pi/4$). -/
noncomputable def dirichletBetaNat (s : ℕ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ n) / ((2 * n + 1 : ℝ) ^ s)

/-- The defining series of `dirichletBetaNat s` is summable whenever $s \ge 2$. -/
@[category API, AMS 11 33]
theorem summable_dirichletBetaNat_term {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => ((-1 : ℝ) ^ n) / ((2 * n + 1 : ℝ) ^ s)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2))
  · exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  · intro n
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    calc
      ((n + 1 : ℝ) ^ 2) ≤ ((2 * n + 1 : ℝ) ^ 2) := by gcongr; linarith
      _ ≤ ((2 * n + 1 : ℝ) ^ s) := pow_le_pow_right₀ (by linarith) hs

/-- At $s = 2$, `dirichletBetaNat 2` is definitionally equal to `catalanConstant`. -/
@[category test, AMS 11 33]
theorem dirichletBetaNat_two_eq_catalanConstant :
    dirichletBetaNat 2 = catalanConstant :=
  rfl

/-- Sanity check at $s = 4$: pairing even and odd terms of the alternating series shows
$80 / 81 \le \beta(4)$. -/
@[category test, AMS 11 33]
theorem eighty_div_eighty_one_le_dirichletBetaNat_four :
    (80 / 81 : ℝ) ≤ dirichletBetaNat 4 := by
  let f : ℕ → ℝ := fun n => ((-1 : ℝ) ^ n) / ((2 * n + 1 : ℝ) ^ 4)
  have hf : Summable f := summable_dirichletBetaNat_term (by norm_num : 2 ≤ 4)
  have he : Summable (fun m => f (2 * m)) := hf.comp_injective (fun _ _ h => by omega)
  have ho : Summable (fun m => f (2 * m + 1)) := hf.comp_injective (fun _ _ h => by omega)
  have htsum : ∑' m : ℕ, (f (2 * m) + f (2 * m + 1)) = dirichletBetaNat 4 := by
    rw [he.tsum_add ho, tsum_even_add_odd he ho]; rfl
  rw [← htsum]
  calc
    (80 / 81 : ℝ) = ∑ m ∈ ({0} : Finset ℕ), (f (2 * m) + f (2 * m + 1)) := by norm_num [f]
    _ ≤ _ := (he.add ho).sum_le_tsum {0} fun m _ => by
        have hpair : f (2 * m) + f (2 * m + 1) =
            1 / ((2 * (2 * m : ℕ) + 1 : ℝ) ^ 4) - 1 / ((2 * (2 * m + 1 : ℕ) + 1 : ℝ) ^ 4) := by
          dsimp [f]; rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]; ring
        rw [hpair, sub_nonneg]
        exact one_div_le_one_div_of_le (by positivity) (by gcongr; omega)

/--
Rivoal and Zudilin [RZ03] proved that $\beta(2k)$ is irrational for infinitely many integers
$k \ge 1$.
-/
@[category research solved, AMS 11 33]
theorem rivoal_zudilin_infinitely_many_even_beta_irrational :
    {k : ℕ | 1 ≤ k ∧ Irrational (dirichletBetaNat (2 * k))}.Infinite := by
  sorry

/--
For every integer $k \ge 2$, the even beta value $\beta(2k)$ is irrational (for $k = 1$, see
`Irrational.irrational_catalanConstant`).
-/
@[category research open, AMS 11 33]
theorem dirichlet_beta_even_irrational {k : ℕ} (hk : 2 ≤ k) :
    Irrational (dirichletBetaNat (2 * k)) := by
  sorry

/--
For every integer $k \ge 2$, the even beta value $\beta(2k)$ is transcendental over $\mathbb{Q}$
(for $k = 1$, see `Transcendental.transcendental_catalanConstant`).
-/
@[category research open, AMS 11 33]
theorem dirichlet_beta_even_transcendental {k : ℕ} (hk : 2 ≤ k) :
    Transcendental ℚ (dirichletBetaNat (2 * k)) := by
  sorry

end DirichletBetaValues
