/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1134

*References:*
- [erdosproblems.com/1134](https://www.erdosproblems.com/1134)
- [La16] Lagarias, Jeffrey C., *Erdős, Klarner, and the $3x+1$ problem*. Amer. Math. Monthly
  (2016), 753--776.
- [KlRa74] Klarner, D. A. and Rado, R., *Arithmetic properties of certain recursively defined
  sets*. Pacific J. Math. (1974), 445--463.
- [Kl82] Klarner, David A., *A sufficient condition for certain semigroups to be free*. J. Algebra
  (1982), 140--148.
- [Gu83b] Guy, Richard K., *Unsolved Problems: Don't Try to Solve These Problems*. Amer. Math.
  Monthly (1983), 35--38+39--41.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

@[expose] public section

namespace Erdos1134

/-- The smallest set of natural numbers which contains `1` and is closed under the operations
`x ↦ 2x + 1`, `x ↦ 3x + 1` and `x ↦ 6x + 1`. -/
def A : Set ℕ :=
  ⋂₀ {S : Set ℕ | 1 ∈ S ∧ ∀ x ∈ S, 2 * x + 1 ∈ S ∧ 3 * x + 1 ∈ S ∧ 6 * x + 1 ∈ S}

/--
Let $A\subseteq \mathbb{N}$ be the smallest set which contains $1$ and is closed under the
operations
$$x\mapsto 2x+1,\quad x\mapsto 3x+1,\quad x\mapsto 6x+1.$$
Does $A$ have positive lower density?

Lagarias [La16] reports that Erdős asked this in 1972, offering £10 for a solution. (Although
Hilton told Lagarias that this problem may have been formulated by Klarner, and that Erdős liked
it and offered a prize for its solution.)

Erdős had earlier proved (as reported in [KlRa74]) that if $A$ is the smallest set which contains
$1$ and is closed under the operations $x\mapsto m_ix+b_i$ for some (possibly infinite) collection
of $m_i\geq 1$ and $b_i\geq 0$ then, if $\sigma>0$ is such that $\sum \frac{1}{m_i^\sigma}=1$
then, for all large $X$, $\lvert A\cap [1,X]\rvert \ll X^{\sigma+o(1)}$. This result does not
help with the given problem since $\frac{1}{2}+\frac{1}{3}+\frac{1}{6}=1$.

This was answered in the negative soon afterwards by Crampin and Hilton (as reported in [Kl82]),
who proved that in fact, for all large $X$, $\lvert A\cap [1,X]\rvert \ll X^{\tau+o(1)}$ where
$\tau\approx 0.900626$ is the unique positive root of
$$6^{-\tau}+\sum_{k\geq 0}(3\cdot 2^k)^{-\tau}=1.$$
Their proof is given in [La16]. This problem is repeated by Guy [Gu83b] in an article called
'Don't Try to Solve These Problems'. This is Problem E36 in Guy's collection [Gu04].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1134.lean#L79"]
theorem erdos_1134 : answer(False) ↔ 0 < A.lowerDensity := by
  sorry

/-- The counting function of $A$ is sublinear: $\lvert A\cap [1,X]\rvert \ll X^{\tau+o(1)}$ with
$\tau < 1$, so in particular $\lvert A \cap [1, X]\rvert \ll X^{19/20}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1134/Dirichlet.lean#L376"]
theorem erdos_1134.variants.sublinear :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, ((A ∩ Set.Iic X).ncard : ℝ) ≤ C * (X : ℝ) ^ (19 / 20 : ℝ) := by
  sorry

/--
Klarner has several (open) variants of this problem - see Section 8.9 of [La16]. For example, it
is unknown if the smallest set $A$ which contains $0$ and is closed under
$$x\mapsto 2x,\quad x\mapsto 3x+2,\quad x\mapsto 6x+3$$
has positive density.
-/
@[category research open, AMS 11]
theorem erdos_1134.variants.klarner : answer(sorry) ↔
    0 < (⋂₀ {S : Set ℕ | 0 ∈ S ∧
      ∀ x ∈ S, 2 * x ∈ S ∧ 3 * x + 2 ∈ S ∧ 6 * x + 3 ∈ S}).lowerDensity := by
  sorry

end Erdos1134
