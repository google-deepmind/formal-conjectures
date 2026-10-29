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
# Erdős Problem 656

*References:*
- [erdosproblems.com/656](https://www.erdosproblems.com/656)
- [Er75b] Erdős, Paul, *Problems and results in combinatorial number theory*. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [KMRR24] Kra, B., Moreira, J., Richter, F. K. and Robertson, D., *A proof of Erdős's $B+B+t$
  conjecture*. Commun. Am. Math. Soc. 4 (2024), 480-494.
  [arXiv:2206.12377](https://arxiv.org/abs/2206.12377)
-/

@[expose] public section

namespace Erdos656

/--
Let $A\subset \mathbb{N}$ be a set with positive upper density. Must there exist an infinite set
$B\subseteq A$ and integer $t$ such that
$$\{b_1+b_2: b_1\neq b_2\in B\}+t\subseteq A?$$

Erdős [Er75b] posed this as a candidate for a density version of Hindman's theorem. This is true,
and was proved by Kra, Moreira, Richter, and Robertson [KMRR24, Theorem 1.2 (i)], even for sets of
positive upper Banach density and with $t \geq 0$.

The inclusion says that every $b_1+b_2+t$ is an element of `A`, as an integer.
-/
@[category research solved, question, AMS 5 11]
theorem erdos_656 :
    ∀ A : Set ℕ, 0 < A.upperDensity →
      ∃ B ⊆ A, B.Infinite ∧ ∃ t : ℤ, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
        ∃ a ∈ A, (a : ℤ) = b₁ + b₂ + t := by
  sorry

end Erdos656
