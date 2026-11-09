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
# Bugeaud Collection of Conjectures and Open Questions: Normality of a Reciprocal to One Base

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Riv08] Rivoal, Tanguy. "On the bits counting function of real numbers."
    Journal of the Australian Mathematical Society 85 (2008): 95-111.
  - [Wal09] Waldschmidt, Michel. "Words and transcendence." In Analytic Number Theory:
    Essays in Honour of Klaus Roth, Cambridge University Press, 2009, 449-470.
    [arXiv:0908.4034](https://arxiv.org/abs/0908.4034).
  - [CG17] Chang, Y., and Gao, X. "Fourier decay bound and differential images of self-similar
    measures." [arXiv:1710.07131](https://arxiv.org/abs/1710.07131) (2017).
  - [Tem26] Temur, Faruk. "Computable construction of absolutely normal numbers with
    non-normal reciprocals." Preprint (2026).
    [ResearchGate](https://www.researchgate.net/publication/414679447_COMPUTABLE_CONSTRUCTION_OF_ABSOLUTELY_NORMAL_NUMBERS_WITH_NON-NORMAL_RECIPROCALS)

Problems 10.17 and 10.18 are questions of Mendès France, recorded by Rivoal [Riv08, p. 106]
and by Waldschmidt [Wal09, Section 6, p. 467]. Problem 10.18 is in `Problem10_18.lean`.

## Status

Both problems are solved by Temur [Tem26, Theorem 1], which gives for every base $b \ge 2$ a
computable absolutely normal $\xi_b > 0$ whose reciprocal is not simply normal to base $b$.
Existence alone is weaker: it follows from the Fourier decay bounds of Chang and Gao
[CG17, Corollary 1.4] applied to $x \mapsto 1/(1 + x)$. Temur [Tem26, Remark 1] notes that
the construction is explicit in the sense of a terminating rule with an approximation
guarantee, not of a feasible algorithm for printing digits.

## Formalisation

`problem_10_17` states the simple normality case with the extra hypothesis that $\xi$ is
irrational, as in the question of Mendès France recorded by Rivoal. The hypothesis is needed:
$1/3$ is simply normal to base $2$, while its reciprocal $3$ has fractional part $0$, so
without it a rational number answers the case $b = 2$; see
`not_isSimplyNormalInBase_two_three`. Normality to base $b$ already forces irrationality, so
the normality case needs no such hypothesis.
-/

@[expose] public section

namespace Bugeaud17

open NormalNumber

/--
Problem 10.17 (simple normality). Let $b \ge 2$ be an integer. There is an irrational
$\xi > 0$ which is simply normal to base $b$ and for which $1/\xi$ is not simply normal to
base $b$. Solved by Temur [Tem26].
-/
@[category research solved, AMS 11]
theorem problem_10_17 (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ : ℝ, 0 < ξ ∧ Irrational ξ ∧ IsSimplyNormalInBase b ξ ∧
      ¬ IsSimplyNormalInBase b ξ⁻¹ := by
  sorry

/--
Problem 10.17 (normality). Let $b \ge 2$ be an integer. There is a $\xi > 0$ which is normal
to base $b$ and for which $1/\xi$ is not normal to base $b$. Solved by Temur [Tem26].
-/
@[category research solved, AMS 11]
theorem problem_10_17.variants.normal (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ : ℝ, 0 < ξ ∧ IsNormalInBase b ξ ∧ ¬ IsNormalInBase b ξ⁻¹ := by
  sorry

/--
The explicit form asked for by Problem 10.17, from Temur [Tem26, Theorem 1]: the number can be
taken computable, and the reciprocal fails even simple normality.
-/
@[category research solved, AMS 3 11]
theorem problem_10_17.variants.computable (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ : ℝ, 0 < ξ ∧ Real.IsComputable ξ ∧ IsNormalInBase b ξ ∧
      ¬ IsSimplyNormalInBase b ξ⁻¹ := by
  sorry

/--
Rivoal [Riv08] observes that the irrationality hypothesis matters: $1/3$ is simply normal to
base $2$, whereas its reciprocal $3$ is an integer, so all base-$2$ digits of $3$ after the
radix point are $0$.
-/
@[category test, AMS 11]
theorem not_isSimplyNormalInBase_two_three : ¬ IsSimplyNormalInBase 2 (3 : ℝ) :=
  not_isSimplyNormalInBase_of_fract_eq_zero le_rfl (by norm_num [Int.fract])

end Bugeaud17
