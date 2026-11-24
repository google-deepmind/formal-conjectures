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
# Lawton's Multivariable Mahler Limit and Boyd's Range Conjectures

Given a nonzero polynomial $P \in \mathbb{C}[X_0, \dots, X_{n-1}]$, its logarithmic Mahler measure
integrates $\log \|P\|$ across the complex unit $n$-torus $\mathbb{T}^n$:
$$m(P) = \int_{[0, 1]^n}
  \log \|P(e^{2\pi i \theta_0}, \dots, e^{2\pi i \theta_{n-1}})\| \, d\theta.$$
David W. Boyd (1981) conjectured—and Wayne M. Lawton (1983) proved—that $m(P)$ equals the limit of
specialized univariate measures $m(P(t^{r_0}, \dots, t^{r_{n-1}}))$ once the shortest nonzero
integer relation norm $q(r) = \min \{ \max_j |s_j| : s \in \mathbb{Z}^n \setminus \{0\},
\sum_j s_j r_j = 0 \}$ grows unboundedly. Writing $L_n$ for the values $m(P)$ over nonzero
$P \in \mathbb{Z}[X_0, \dots, X_{n-1}]$ and $L_\infty = \bigcup_n L_n$, Boyd conjectured both that
$L_\infty$ is closed in $\mathbb{R}$ (which implies
`LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem`) and that
$L_1 \subsetneq L_2 \subsetneq L_3 \subsetneq \cdots$. Christopher J. Smyth (1981) established
$m(1 + X_0 + X_1 + X_2) = \frac{7}{2\pi^2} \zeta(3)$.

*References:*
- [Wikipedia: Mahler measure](https://en.wikipedia.org/wiki/Mahler_measure)
- D. W. Boyd (1981), Canad. Math. Bull. **24**, no. 4, 453–469, DOI: `10.4153/cmb-1981-069-5`.
- C. J. Smyth (1981), Bull. Austral. Math. Soc. **23**, no. 1, 49–63.
- W. M. Lawton (1983), J. Number Theory **16**, no. 3, 356–362,
  DOI: `10.1016/0022-314X(83)90063-X`.
-/

@[expose] public section

namespace MultivariableMahlerMeasure

open MeasureTheory MvPolynomial

/-- Univariate circle integral
$\int_0^1 \log \|P(e^{2\pi i r_0 t}, \dots, e^{2\pi i r_{n-1} t})\| \, dt$
associated with an exponent tuple $r \in \mathbb{Z}^n$. -/
noncomputable def univariateSpecLogMahler {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (r : Fin n → ℤ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, Real.log ‖MvPolynomial.eval (torusPoint (fun j ↦ (r j : ℝ) * t)) P‖

/-- Lawton's relation-norm condition $q(r) > B$: every nonzero integer tuple $s \in \mathbb{Z}^n$
satisfying $\sum_j s_j r_j = 0$ has some coordinate with $|s_j| > B$. -/
def HasNoShortRelation {n : ℕ} (B : ℕ) (r : Fin n → ℤ) : Prop :=
  ∀ s : Fin n → ℤ, s ≠ 0 → ∑ j, s j * r j = 0 → ∃ j, (B : ℤ) < |s j|

/-- Boyd's value set $L_n = \{m(P) : P \in \mathbb{Z}[X_0, \dots, X_{n-1}] \setminus \{0\}\}$. -/
def intLogMahlerSet (n : ℕ) : Set ℝ :=
  {m : ℝ | ∃ P : MvPolynomial (Fin n) ℤ,
    P ≠ 0 ∧ m = logMahlerMeasure (MvPolynomial.map (Int.castRingHom ℂ) P)}

/-- On constant polynomials, `univariateSpecLogMahler` agrees with univariate
`(Polynomial.C c).logMahlerMeasure`. -/
@[category API, AMS 11]
theorem univariateSpecLogMahler_const {n : ℕ} (c : ℂ) (r : Fin n → ℤ) :
    univariateSpecLogMahler (MvPolynomial.C c : MvPolynomial (Fin n) ℂ) r =
      (Polynomial.C c).logMahlerMeasure := by
  unfold univariateSpecLogMahler
  simp [Measure.real, Polynomial.logMahlerMeasure_const]

/-- Every value set $L_n$ contains $0$, witnessed by the constant polynomial $1$. -/
@[category test, AMS 11]
theorem zero_mem_intLogMahlerSet (n : ℕ) : 0 ∈ intLogMahlerSet n :=
  ⟨1, one_ne_zero, by simpa using (logMahlerMeasure_monomial_one (0 : Fin n →₀ ℕ)).symm⟩

/-- Boyd's pair $(1, N)$ satisfies `HasNoShortRelation B` whenever $N > B$. -/
@[category test, AMS 11]
theorem hasNoShortRelation_boyd_pair (B : ℕ) (N : ℤ) (hBN : (B : ℤ) < N) :
    HasNoShortRelation B ![1, N] := by
  intro s hs hsum
  rw [Fin.sum_univ_two] at hsum
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one] at hsum
  by_cases hs1 : s 1 = 0
  · exact False.elim <| hs <| by ext i; fin_cases i <;> simp_all
  · refine ⟨0, ?_⟩
    have h0 : s 0 = -(s 1 * N) := by linarith
    have habs1 : 1 ≤ |s 1| := Int.one_le_abs hs1
    have hNpos : 0 ≤ N := by linarith
    have habs0 : |s 0| = |s 1| * N := by
      rw [h0, abs_neg, abs_mul, abs_of_nonneg hNpos]
    nlinarith

/-- The degenerate tuple $(1, 0)$ fails `HasNoShortRelation 1`. -/
@[category test, AMS 11]
theorem not_hasNoShortRelation_one_zero : ¬ HasNoShortRelation 1 ![1, 0] := by
  intro h
  have hs : (![(0 : ℤ), 1] : Fin 2 → ℤ) ≠ 0 := by
    intro h0
    have h1 := congr_fun h0 1
    norm_num at h1
  rcases h ![0, 1] hs (by simp [Fin.sum_univ_two]) with ⟨j, hj⟩
  fin_cases j <;> norm_num at hj

/-- **Lawton's Multivariable Limit Theorem** (conjectured by Boyd 1981, proved by Lawton 1983):
for every nonzero $P \in \mathbb{C}[X_0, \dots, X_{n-1}]$ and $\varepsilon > 0$, some threshold
$B \in \mathbb{N}$ ensures $|m(P(t^{r_0}, \dots, t^{r_{n-1}})) - m(P)| < \varepsilon$ whenever
$q(r) > B$. -/
@[category research solved, AMS 11]
theorem lawton_multivariable_mahler_measure_limit {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : P ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ r : Fin n → ℤ, HasNoShortRelation B r →
      |univariateSpecLogMahler P r - logMahlerMeasure P| < ε := by
  sorry

/-- **Smyth's Linear Mahler Formula** (1981): $1 + X_0 + X_1 + X_2$ has logarithmic measure
$\frac{7}{2\pi^2} \zeta(3)$. -/
@[category research solved, AMS 11]
theorem smyth_three_variable_linear_mahler_measure :
    logMahlerMeasure
        (1 + MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) =
      7 / (2 * Real.pi ^ 2) * (riemannZeta 3).re := by
  sorry

/-- **Boyd's Closedness Conjecture** (1981): $L_\infty = \bigcup_{n \in \mathbb{N}} L_n$ (which
equals $\bigcup_{n \ge 1} L_n$ since $L_0 \subseteq L_1$ via constant polynomials) is closed inside
$\mathbb{R}$. This implies `LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem`. -/
@[category research open, AMS 11]
theorem boyd_mahler_measure_set_closed_conjecture :
    IsClosed (⋃ n, intLogMahlerSet n) := by
  sorry

/-- **Boyd's Strict Hierarchy Conjecture** (1981): every dimension $n \ge 1$ satisfies the strict
inclusion $L_n \subsetneq L_{n + 1}$ (note $n = 0$ is excluded because $L_0 \subsetneq L_1$ holds
unconditionally). -/
@[category research open, AMS 11]
theorem boyd_mahler_measure_strict_hierarchy_conjecture {n : ℕ} (hn : 1 ≤ n) :
    intLogMahlerSet n ⊂ intLogMahlerSet (n + 1) := by
  sorry

end MultivariableMahlerMeasure
