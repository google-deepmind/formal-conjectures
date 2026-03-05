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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 296

*Reference:* [erdosproblems.com/296](https://www.erdosproblems.com/296)

Let $N \geq 1$ and let $k(N)$ be maximal such that there exist $k$ pairwise disjoint
$A_1, \ldots, A_k \subseteq \{1, \ldots, N\}$ with $\sum_{n \in A_i} 1/n = 1$ for all $i$.

Erdős and Graham [ErGr80] asked: Estimate $k(N)$. Is it true that $k(N) = o(\log N)$?

Hunter and Sawhney observed that Theorem 3 of Bloom [Bl21], coupled with the
trivial greedy approach, implies $k(N) = (1 - o(1)) \log N$. In particular,
$k(N)$ is not $o(\log N)$; it grows like $\log N$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Bl21] Bloom, T., *On a density conjecture about unit fractions*. (2021).
-/

open Finset BigOperators

namespace Erdos296

/-- The reciprocal sum $\sum_{n \in A} 1/n$ of a finite set of natural numbers. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / (n : ℚ)

/--
Erdős Problem 296 [ErGr80] (resolved by Hunter–Sawhney via Bloom [Bl21]):

$k(N) = (1 - o(1)) \log N$, where $k(N)$ is the maximum number of pairwise
disjoint subsets of $\{1, \ldots, N\}$ whose reciprocal sums each equal $1$.

We formalize the non-trivial lower bound: for every $\varepsilon > 0$, for all
sufficiently large $N$, one can find at least $\lfloor (1 - \varepsilon) \ln N \rfloor$
pairwise disjoint subsets of $\{1, \ldots, N\}$, each with reciprocal sum exactly $1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_296 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ (k : ℕ) (family : Fin k → Finset ℕ),
        (k : ℝ) ≥ (1 - ε) * Real.log (N : ℝ) ∧
        (∀ i, family i ⊆ Finset.Icc 1 N) ∧
        (∀ i j, i ≠ j → Disjoint (family i) (family j)) ∧
        (∀ i, reciprocalSum (family i) = 1) := by
  sorry

end Erdos296
