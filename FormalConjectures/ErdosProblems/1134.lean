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
# Erdős Problem 1134

*References:*
- [erdosproblems.com/1134](https://www.erdosproblems.com/1134)
- [Gu82] Guy, R. K., [letter to N. J. A. Sloane (1982)](https://oeis.org/A005658/a005658.pdf#page=2).
- [La10] Lagarias, J. C., [*The $3x+1$ Problem: An Overview*](https://arxiv.org/pdf/2111.02635#page=4),
  p. 4.
- [Ka26] Kalmynin, A., [*Klarner's sequences have density $0$*](https://arxiv.org/pdf/2611.22034#page=4),
  Theorems 3 and 4 (2026).
- [OEIS A005658](https://oeis.org/A005658)
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

set_option linter.style.formal_proof_palomar false in
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
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1134.lean#L79"]
theorem erdos_1134 : ¬ 0 < A.lowerDensity := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The counting function of $A$ is sublinear: $\lvert A\cap [1,X]\rvert \ll X^{\tau+o(1)}$ with
$\tau < 1$, so in particular $\lvert A \cap [1, X]\rvert \ll X^{19/20}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1134/Dirichlet.lean#L376"]
theorem erdos_1134.variants.sublinear :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, ((A ∩ Set.Iic X).ncard : ℝ) ≤ C * (X : ℝ) ^ (19 / 20 : ℝ) := by
  sorry

/-- The smallest set containing $s$ and closed under $x \mapsto 2x$, $x \mapsto 3x+2$,
and $x \mapsto 6x+3$. -/
def klarnerOrbit (s : ℕ) : Set ℕ :=
  ⋂₀ {S : Set ℕ | s ∈ S ∧ ∀ x ∈ S, 2 * x ∈ S ∧ 3 * x + 2 ∈ S ∧ 6 * x + 3 ∈ S}

/-- The two starting values give different orbits even away from the starting values themselves. -/
@[category API, AMS 11]
theorem klarnerOrbit_separating_elements :
    3 ∈ klarnerOrbit 0 \ klarnerOrbit 1 ∧ 5 ∈ klarnerOrbit 1 \ klarnerOrbit 0 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro S hS
    exact (hS.2 0 hS.1).2.2
  · intro h
    refine (h {n : ℕ | n ≠ 0 ∧ n ≠ 3} ⟨by decide, ?_⟩).2 rfl
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    omega
  · intro S hS
    exact (hS.2 1 hS.1).2.1
  · intro h
    refine (h {n : ℕ | n ≠ 1 ∧ n ≠ 5} ⟨by decide, ?_⟩).2 rfl
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    omega

set_option linter.style.formal_proof_palomar false in
/-- The version on erdosproblems.com starts from $0$. Kenta Kitamura proved in Lean that
this orbit has natural density zero. -/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/KitaKen1/erdos-1134-lean/blob/57042c7e43ae71cd7008e461cf3b9d81b8d8a20f/lean/Erdos1134KlarnerFC.lean#L2110-L2113"]
theorem erdos_1134.variants.klarner : ¬ 0 < (klarnerOrbit 0).lowerDensity := by
  sorry

/-- Does the orbit starting from $1$ have positive lower density? Guy [Gu82] gives this
starting value and the first terms of OEIS A005658. Lagarias [La10, p. 4] states the question
using lower density.
Kalmynin [Ka26, Theorem 3] proves lower density zero for the orbit of every seed set of density
zero. Taking the singleton $\{1\}$ answers the question. Its bounded counting function also
satisfies the hypothesis of [Ka26, Theorem 4], giving natural density zero. -/
@[category research solved, question, AMS 11]
theorem erdos_1134.variants.klarner_seed_one : ¬ 0 < (klarnerOrbit 1).lowerDensity := by
  sorry

end Erdos1134
