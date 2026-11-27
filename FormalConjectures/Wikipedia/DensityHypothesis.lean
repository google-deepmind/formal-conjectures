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
# Density hypothesis for Riemann zeta zeros

For $\frac{1}{2} \le \sigma \le 1$ and $T \ge 2$, let $N(\sigma, T)$ count the zeros
$\rho = \beta + i\gamma$ of $\zeta(s)$ (with multiplicity) inside $\sigma \le \beta \le 1$ and
$0 < \gamma \le T$. (Classical sources often count $|\gamma| \le T$; by conjugate symmetry of
$\zeta(s)$ and nonvanishing on $\mathbb{R} \cap [1/2, 1]$, this differs only by a factor of $2$ and
leaves $O_\varepsilon$ bounds unchanged.) The Density Hypothesis states that
$N(\sigma, T) = O_\varepsilon(T^{2(1 - \sigma) + \varepsilon})$ uniformly over
$\frac{1}{2} \le \sigma \le 1$ for every $\varepsilon > 0$. Either the Riemann Hypothesis or
Lindelöf's hypothesis implies this estimate. Alpöge proved the Riemann Hypothesis [Al26]. Unconditional bounds of the shape
$N(\sigma, T) = O_\varepsilon(T^{A(\sigma)(1 - \sigma) + \varepsilon})$ were proved by Ingham
(1940) with $A(\sigma) = \frac{3}{2 - \sigma}$, Huxley (1972) with
$A(\sigma) = \frac{3}{3\sigma - 1}$, and Guth and Maynard (2024) with
$A(\sigma) = \frac{15}{5\sigma + 3}$; combining Ingham's bound for $\sigma \le \frac{7}{10}$ with
Guth and Maynard's bound for $\sigma \ge \frac{7}{10}$ yields the uniform exponent $\frac{30}{13}$.

*References:*
- [Al26] L. Alpöge, [Note on the Riemann Hypothesis](https://alpo.ge/remark.pdf), 2026.
- [Wikipedia](https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis#The_density_hypothesis)
- A. E. Ingham, *On the estimation of $N(\sigma, T)$*, Quart. J. Math. Oxford Ser. **11** (1940),
  DOI: `10.1093/qmath/os-11.1.201`.
- M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. **15** (1972),
  164–170.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*, arXiv:2405.20552
  (2024).
-/

@[expose] public section

namespace DensityHypothesis

/-- Multiplicity-weighted count $N(\sigma, T)$ of zeros of $\zeta(s)$ inside
$\{s \in \mathbb{C} \mid \sigma \le \operatorname{Re}(s) \le 1 \text{ and } 0 <
\operatorname{Im}(s) \le T\}$ (half the symmetric count $|\operatorname{Im}(s)| \le T$). -/
noncomputable abbrev zetaZeroCount (σ T : ℝ) : ℕ :=
  Complex.zeroCountOn riemannZeta
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T}

/-- For nonpositive height $T \le 0$, the rectangle $0 < \operatorname{Im}(s) \le T$ is empty, so
`zetaZeroCount σ T = 0`. -/
@[category test, AMS 11 30]
theorem zetaZeroCount_eq_zero_of_nonpos {σ T : ℝ} (hT : T ≤ 0) :
    zetaZeroCount σ T = 0 :=
  Complex.zeroCountOn_eq_zero_of_forall_ne_zero fun _ hs => by linarith [hs.2.2.1, hs.2.2.2]

/-- Whenever $\sigma > 1$, the strip $\sigma \le \operatorname{Re}(s) \le 1$ is empty, so
`zetaZeroCount σ T = 0`. -/
@[category API, AMS 11 30]
theorem zetaZeroCount_eq_zero_of_one_lt {σ T : ℝ} (hσ : 1 < σ) :
    zetaZeroCount σ T = 0 :=
  Complex.zeroCountOn_eq_zero_of_forall_ne_zero fun _ hs => by linarith [hs.1, hs.2.1]

/-- If $\zeta(s)$ has no zeros in $\{s \in \mathbb{C} \mid \sigma \le \operatorname{Re}(s) \le 1
\text{ and } 0 < \operatorname{Im}(s) \le T\}$, then `zetaZeroCount σ T = 0`. -/
@[category API, AMS 11 30]
theorem zetaZeroCount_eq_zero_of_no_zeros {σ T : ℝ}
    (h : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → 0 < s.im → s.im ≤ T → riemannZeta s ≠ 0) :
    zetaZeroCount σ T = 0 :=
  Complex.zeroCountOn_eq_zero_of_forall_ne_zero fun s hs => h s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/-- Nonvanishing of $\zeta(s)$ on $\operatorname{Re}(s) \ge 1$ gives `zetaZeroCount 1 T = 0`. -/
@[category API, AMS 11 30]
theorem zetaZeroCount_one (T : ℝ) : zetaZeroCount 1 T = 0 :=
  zetaZeroCount_eq_zero_of_no_zeros fun _ hs1 _ _ _ => riemannZeta_ne_zero_of_one_le_re hs1

/-- Compactness guarantees that the counted zero set is finite for all
$\sigma, T \in \mathbb{R}$. -/
@[category API, AMS 11 30]
theorem zetaZeroSet_finite (σ T : ℝ) :
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0}.Finite := by
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
      (Set.Icc σ 1 ×ˢ Set.Icc 0 T)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  refine hK.inter_riemannZetaZeros_finite.subset fun s hs => ?_
  refine ⟨⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, ⟨hs.2.2.1.le, hs.2.2.2.1⟩⟩, ?_⟩, hs.2.2.2.2⟩
  simp [mul_comm Complex.I, Complex.re_add_im]

set_option linter.style.formal_proof_palomar false in
/-- Density Hypothesis: for every $\varepsilon > 0$, there exists $C > 0$ such that
$N(\sigma, T) \le C \, T^{2(1 - \sigma) + \varepsilon}$ for all $\frac{1}{2} \le \sigma \le 1$
and $T \ge 2$. -/
@[category research solved, AMS 11 30, formal_proof using lean4 at
  "https://github.com/senamakel/density-rh/blob/91ffb87856da458ef93fcc139af0d1d389a82af2/Unconditional/DensityUnconditional.lean#L11"]
theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  sorry

/-- Guth–Maynard zero-density bound (2024): for every $\varepsilon > 0$, there exists $C > 0$ such
that $N(\sigma, T) \le C \, T^{\frac{30}{13}(1 - \sigma) + \varepsilon}$ for all
$\frac{1}{2} \le \sigma \le 1$ and $T \ge 2$. -/
@[category research solved, AMS 11 30]
theorem guth_maynard_zero_density (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) := by
  sorry

end DensityHypothesis
