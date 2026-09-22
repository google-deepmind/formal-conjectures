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

import FormalConjecturesUtil

/-!
# Bugeaud Collection of Conjectures and Open Questions: Simultaneously Small Entropies

A real number can be described by its continued fraction expansion and by its expansion in an
integer base. Problem 10.53 asks for an irrational number for which both descriptions have small
block complexity. Temur [Tem26] answered it, in the stronger form that asks for every base at
once, by an explicit construction.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Tem26](https://arxiv.org/abs/2609.16362) Temur, Faruk. "Simultaneously small continued
    fraction entropy and base $b$ entropy." arXiv preprint arXiv:2609.16362 (2026).
  - [BBFKW10] Broderick, Ryan, Yann Bugeaud, Lior Fishman, Dmitry Kleinbock, and Barak Weiss.
    "Schmidt's game, fractals, and numbers normal to no base."
    Mathematical Research Letters 17.2 (2010): 307-321.
-/

namespace Bugeaud53

open Real

/--
Problem 10.53. There is an irrational real number $\xi$ such that $E(\xi) < \log 2$ and
$E(\xi, b) < \log b$ for some integer $b \ge 2$. Answered by Temur [Tem26].
-/
@[category research solved, AMS 11 37]
theorem problem_10_53 :
    ∃ ξ : ℝ, Irrational ξ ∧ cfEntropy ξ < (Real.log 2 : EReal) ∧
      ∃ b : ℕ, 2 ≤ b ∧ baseEntropy b ξ < (Real.log b : EReal) := by
  sorry

/--
Problem 10.53, in the stronger form that asks for every base at once: there is an irrational
real number $\xi$ such that $E(\xi) < \log 2$ and $E(\xi, b) < \log b$ for every integer
$b \ge 2$. Answered by Temur [Tem26].
-/
@[category research solved, AMS 11 37]
theorem problem_10_53.variants.all_bases :
    ∃ ξ : ℝ, Irrational ξ ∧ cfEntropy ξ < (Real.log 2 : EReal) ∧
      ∀ b : ℕ, 2 ≤ b → baseEntropy b ξ < (Real.log b : EReal) := by
  sorry

/--
There are uncountably many numbers as in Problem 10.53. This follows from a result of Broderick,
Bugeaud, Fishman, Kleinbock and Weiss [BBFKW10] applied to the Gauss-Cantor set
$\{[0; 1, a_1, 1, a_2, \ldots] : a_j \in \{1, 2\}\}$, as observed in [Tem26].
-/
@[category research solved, AMS 11 37]
theorem problem_10_53.variants.uncountable :
    ¬ {ξ : ℝ | Irrational ξ ∧ cfEntropy ξ < (Real.log 2 : EReal) ∧
      ∀ b : ℕ, 2 ≤ b → baseEntropy b ξ < (Real.log b : EReal)}.Countable := by
  sorry

/--
Temur [Tem26], Theorem 1. There is an irrational $\xi \in (0, 1)$ all of whose partial quotients
are $1$ or $2$, such that
$$\lVert b^k \xi \rVert > 154^{-2^b} \quad (b \ge 2,\ k \ge 0),$$
where $\lVert \cdot \rVert$ denotes the distance to the nearest integer. The bound on the partial
quotients gives $E(\xi) \le (\log 2) / 4$, and the displayed inequality forces the base $b$
expansion of $\xi$ to omit a block of zeros, which gives $E(\xi, b) < \log b$ for every
$b \ge 2$. Temur's $\xi$ is moreover computable.
-/
@[category research solved, AMS 11 37]
theorem problem_10_53.variants.temur :
    ∃ ξ : ℝ, Irrational ξ ∧ ξ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ n : ℕ, partQuot ξ n = 1 ∨ partQuot ξ n = 2) ∧
      (∀ b : ℕ, 2 ≤ b → ∀ k : ℕ,
        (154 : ℝ) ^ (-(2 ^ b) : ℤ) < distToNearestInt ((b : ℝ) ^ k * ξ)) ∧
      cfEntropy ξ ≤ ((Real.log 2 / 4 : ℝ) : EReal) ∧
      ∀ b : ℕ, 2 ≤ b → baseEntropy b ξ < (Real.log b : EReal) := by
  sorry

end Bugeaud53
