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
# Erdős Problem 670

*Reference:* [erdosproblems.com/670](https://www.erdosproblems.com/670)

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
geometry_. (1997)
-/

open Metric

namespace Erdos670

/--
All pairwise distances in a finite point set are separated by at least $1$:
for any two distinct unordered pairs $\{a, b\}$ and $\{c, d\}$ of points from $A$
(where $a \neq b$ and $c \neq d$), $|d(a, b) - d(c, d)| \geq 1$.
-/
def AllPairwiseDistsSeparatedByOne {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) : Prop :=
  ∀ a b c d : X, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≠ b → c ≠ d →
    (a ≠ c ∨ b ≠ d) → (a ≠ d ∨ b ≠ c) →
    |dist a b - dist c d| ≥ 1

/--
Let $A \subseteq \mathbb{R}^d$ be a set of $n$ points such that all pairwise distances differ by
at least $1$. Is the diameter of $A$ at least $(1 + o(1))n^2$?

The lower bound of $\binom{n}{2}$ for the diameter is trivial. Erdős [Er97f] proved
the claim when $d = 1$.

Formalized as: for every $\varepsilon > 0$, there exists $N$ such that for all $n \geq N$, for
every dimension $d$ and every set $A$ of $n$ points in $\mathbb{R}^d$ with all pairwise
distances differing by at least $1$, the diameter of $A$ is at least $(1 - \varepsilon) \cdot n^2$.
-/
@[category research open, AMS 52]
theorem erdos_670 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ d : ℕ,
          ∀ A : Finset (EuclideanSpace ℝ (Fin d)),
            A.card = n →
            AllPairwiseDistsSeparatedByOne A →
            (1 - ε) * (n : ℝ) ^ 2 ≤
              Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  sorry

end Erdos670
