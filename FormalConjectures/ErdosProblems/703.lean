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
# Erdős Problem 703

*Reference:* [erdosproblems.com/703](https://www.erdosproblems.com/703)

Let $T(n, r)$ be the maximum size of a family of subsets of $\{1, \ldots, n\}$ such that no two
distinct members intersect in exactly $r$ elements. The conjecture, proved by Frankl and Rödl,
asserts that for every $\varepsilon > 0$ there exists $\delta > 0$ such that
$T(n, r) < (2 - \delta)^n$ whenever $\varepsilon n < r < (1/2 - \varepsilon) n$.

This problem carried a **$250 prize**.

See also: Problem 702.

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975, p. 108.
[Er76b] Erdős, P., _Problems in combinatorial and graph theory_ (1976).
[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_, 1981.
[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_, 1982.
[Fr77b] Frankl, P., _An intersection problem for finite sets_, Acta Math. Acad. Sci. Hungar.
(1977), 371–373.
[FrFu84b] Frankl, P. and Füredi, Z., _On hypergraphs without two edges intersecting in a given
number of vertices_, J. Combin. Theory Ser. A (1984), 230–236.
[FrRo87] Frankl, P. and Rödl, V., _Forbidden intersections_, Trans. Amer. Math. Soc. 300 (1987),
259–286.
[FrWi81] Frankl, P. and Wilson, R. M., _Intersection theorems with geometric consequences_,
Combinatorica 1 (1981), 357–368.
-/

open Finset

namespace Erdos703

/-- $T(n, r)$ is the maximum cardinality of a family $\mathcal{F}$ of subsets of
$\{1, \ldots, n\}$ (represented as `Fin n`) such that $|A \cap B| \neq r$ for all distinct
$A, B \in \mathcal{F}$. -/
noncomputable def T (n r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset (Finset (Fin n)),
    F.card = k ∧
    ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≠ r}

/--
Erdős Problem 703 (Frankl–Rödl theorem):

Let $r \geq 1$ and define $T(n,r)$ to be the maximum size of a family $\mathcal{F}$ of subsets
of $\{1, \ldots, n\}$ such that $|A \cap B| \neq r$ for all distinct $A, B \in \mathcal{F}$.

For every $\varepsilon > 0$ there exists $\delta > 0$ such that for all $n$ and $r$ with
$\varepsilon n < r < (1/2 - \varepsilon) n$, we have $T(n,r) < (2 - \delta)^n$.

Proved by Frankl and Rödl [FrRo87].
-/
@[category research solved, AMS 5]
theorem erdos_703 :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧
      ∀ n : ℕ, ∀ r : ℕ,
        ε * (n : ℝ) < (r : ℝ) →
        (r : ℝ) < (1 / 2 - ε) * (n : ℝ) →
        (T n r : ℝ) < (2 - δ) ^ n := by
  sorry

end Erdos703
