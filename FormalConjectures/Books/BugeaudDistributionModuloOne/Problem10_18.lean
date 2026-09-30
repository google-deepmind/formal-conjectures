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
# Bugeaud Collection of Conjectures and Open Questions: Absolute Normality of a Reciprocal

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Riv08] Rivoal, Tanguy. "On the bits counting function of real numbers."
    Journal of the Australian Mathematical Society 85 (2008): 95-111.
  - [Wal09] Waldschmidt, Michel. "Words and transcendence." In Analytic Number Theory:
    Essays in Honour of Klaus Roth, Cambridge University Press, 2009, 449-470.
    [arXiv:0908.4034](https://arxiv.org/abs/0908.4034).
  - [BM22] Becher, Verónica, and Madritsch, Manfred G. "On a question of Mendès France on
    normal numbers." Acta Arithmetica 203 (2022): 271-288.
  - [CG17] Chang, Y., and Gao, X. "Fourier decay bound and differential images of self-similar
    measures." [arXiv:1710.07131](https://arxiv.org/abs/1710.07131) (2017).
  - [Tem26] Temur, Faruk. "Computable construction of absolutely normal numbers with
    non-normal reciprocals." Preprint (2026).
    [ResearchGate](https://www.researchgate.net/publication/414679447_COMPUTABLE_CONSTRUCTION_OF_ABSOLUTELY_NORMAL_NUMBERS_WITH_NON-NORMAL_RECIPROCALS)

This is the absolute version of Problem 10.17, which is in `Problem10_17.lean`. Both are
questions of Mendès France, recorded by Rivoal [Riv08, p. 106] and by Waldschmidt
[Wal09, Section 6, p. 467].

## Status

Solved by Temur [Tem26, Theorem 1]: for every base $b \ge 2$ there is a computable absolutely
normal $\xi_b > 0$ whose reciprocal is not simply normal to base $b$, hence not absolutely
normal. Existence alone is weaker: it follows from the Fourier decay bounds of Chang and Gao
[CG17, Corollary 1.4] applied to $x \mapsto 1/(1 + x)$. Temur [Tem26, Remark 1] notes that the
construction is explicit in the sense of a terminating rule with an approximation guarantee,
not of a feasible algorithm for printing digits.

A different reciprocal question of Mendès France, also recorded by Rivoal, asks for a
computable $\xi$ such that $\xi$ and $1/\xi$ are both absolutely normal. That one was answered
by Becher and Madritsch [BM22] and is not Problem 10.18.
-/

@[expose] public section

namespace Bugeaud18

open NormalNumber

/--
Problem 10.18. There is a positive real number $\xi$ which is absolutely normal and for which
$1/\xi$ is not absolutely normal. Solved by Temur [Tem26].
-/
@[category research solved, AMS 11]
theorem problem_10_18 :
    ∃ ξ : ℝ, 0 < ξ ∧ IsAbsolutelyNormal ξ ∧ ¬ IsAbsolutelyNormal ξ⁻¹ := by
  sorry

/--
The explicit form asked for by Problem 10.18, from Temur [Tem26, Theorem 1]: for each base
$b \ge 2$ the number can be taken computable, and its reciprocal fails even simple normality
to base $b$. For $b \ge 3$ the digit $b - 1$ does not occur in the base-$b$ expansion of
$1/\xi$, and for $b = 2$ the digit $1$ has upper frequency at most $1/3$.
-/
@[category research solved, AMS 3 11]
theorem problem_10_18.variants.computable (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ : ℝ, 0 < ξ ∧ Real.IsComputable ξ ∧ IsAbsolutelyNormal ξ ∧
      ¬ IsSimplyNormalInBase b ξ⁻¹ := by
  sorry

/--
Sanity check: the failure of absolute normality asked for by Problem 10.18 is satisfiable. An
integer is not absolutely normal, since all of its digits after the radix point are $0$.
-/
@[category test, AMS 11]
theorem not_isAbsolutelyNormal_three : ¬ IsAbsolutelyNormal (3 : ℝ) := fun h =>
  not_isSimplyNormalInBase_of_fract_eq_zero (b := 2) le_rfl (by norm_num [Int.fract])
    (h 2 le_rfl).isSimplyNormalInBase

end Bugeaud18
