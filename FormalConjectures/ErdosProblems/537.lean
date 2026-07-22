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
# Erdős Problem 537

*References:*
- [erdosproblems.com/537](https://www.erdosproblems.com/537)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of combinatorial
  theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.
-/

open Filter

namespace Erdos537

/--
Let $\epsilon>0$ and $N$ be sufficiently large. If $A\subseteq \{1,\ldots,N\}$ has
$\lvert A\rvert \geq \epsilon N$ then must there exist $a_1,a_2,a_3\in A$ and distinct primes
$p_1,p_2,p_3$ such that
\[a_1p_1=a_2p_2=a_3p_3?\]

A positive answer would imply [536].

Erdős describes a construction of Ruzsa which disproves this: consider the set of all
squarefree numbers of the shape $p_1\cdots p_r$ where $p_{i+1}>2p_i$ for $1\leq i<r$. This
set has positive density, and hence if $A$ is its intersection with $(N/2,N)$ then
$\lvert A\rvert \gg N$ for all large $N$. Suppose now that $p_1a_1=p_2a_2=p_3a_3$ where
$a_i\in A$ and $p_1,p_2,p_3$ are distinct primes. Without loss of generality we may assume
that $a_2>a_3$ and hence $p_2<p_3$, and so since $p_2p_3\mid a_1\in A$ we must have
$2<p_3/p_2$. On the other hand $p_3/p_2=a_2/a_3\in (1,2)$, a contradiction.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos537.lean"]
theorem erdos_537 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃ : ℕ,
          p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃ := by
  sorry

end Erdos537
