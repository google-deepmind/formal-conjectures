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
$\beta(2), \beta(4), \dots, \beta(12)$ is irrational.

Wikipedia remarks only that the rationality or algebraicity of general even beta values remains
undetermined, and [Zu19] explicitly states irrationality and transcendence expectations only for
Catalan's constant $G = \beta(2)$ (formalized for $k = 1$ as the open conjectures
`Irrational.irrational_catalanConstant` and `Transcendental.transcendental_catalanConstant`). For
general $k \ge 1$, irrationality of $\beta(2k) = 4^{-2k} (\zeta(2k, 1/4) - \zeta(2k, 3/4))$
follows from the Strong Chowla–Milnor conjecture of Gun, Murty, and Rath [GMR11] over $\mathbb{Q}$
at modulus $4$, while transcendence of $\beta(2k)$ follows from Grothendieck's period conjecture
on the motivic fundamental group of $\mathbf{G}_m - \mu_4$ via polylogarithms at fourth roots of
unity, $2 i \beta(2k) = \operatorname{Li}_{2k}(i) - \operatorname{Li}_{2k}(-i)$ [De10, Wa06].

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Dirichlet_beta_function#Specific_values)
- [RZ03] T. Rivoal and W. Zudilin, *Diophantine properties of numbers related to Catalan's
  constant*, Math. Ann. **326** (2003), no. 4, 705–721.
- [Wa06] M. Waldschmidt, *Transcendence of periods: the state of the art*, Pure Appl. Math. Q.
  **2** (2006), no. 2, 435–463.
- [De10] P. Deligne, *Le groupe fondamental unipotent motivique de $\mathbf{G}_m - \mu_N$, pour
  $N = 2, 3, 4, 6$ ou $8$*, Publ. Math. Inst. Hautes Études Sci. **112** (2010), 101–141.
- [GMR11] S. Gun, M. R. Murty, and P. Rath, *On a conjecture of Chowla and Milnor*, Canad. J.
  Math. **63** (2011), no. 6, 1328–1344.
- [Zu19] W. Zudilin, *Arithmetic of Catalan's constant and its relatives*, Abh. Math. Semin. Univ.
  Hambg. **89** (2019), no. 1, 45–53.
-/

@[expose] public section

namespace DirichletBetaValues

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
Zudilin [Zu19] established irrationality for some value among
$\beta(2), \beta(4), \beta(6), \beta(8), \beta(10), \beta(12)$.
-/
@[category research solved, AMS 11 33]
theorem zudilin_exists_irrational_even_beta_le_twelve :
    ∃ k ∈ Finset.Icc 1 6, Irrational (dirichletBetaNat (2 * k)) := by
  sorry

/--
For every integer $k \ge 2$, the even beta value $\beta(2k)$ is irrational, as predicted by the
Strong Chowla–Milnor conjecture [GMR11] at modulus $4$ (for $k = 1$, see
`Irrational.irrational_catalanConstant`).
-/
@[category research open, AMS 11 33]
theorem dirichlet_beta_even_irrational {k : ℕ} (hk : 2 ≤ k) :
    Irrational (dirichletBetaNat (2 * k)) := by
  sorry

/--
For every integer $k \ge 2$, the even beta value $\beta(2k)$ is transcendental over $\mathbb{Q}$,
as predicted by Grothendieck's period conjecture on the motivic fundamental group of
$\mathbf{G}_m - \mu_4$ via polylogarithms at fourth roots of unity [De10, Wa06] (for $k = 1$, see
`Transcendental.transcendental_catalanConstant`).
-/
@[category research open, AMS 11 33]
theorem dirichlet_beta_even_transcendental {k : ℕ} (hk : 2 ≤ k) :
    Transcendental ℚ (dirichletBetaNat (2 * k)) := by
  sorry

end DirichletBetaValues
