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
# Erdős Problem 613

Must every graph on $\binom{2n+1}{2} - \binom{n}{2} - 1$ edges (for $n \geq 3$) be expressible
as the union of a bipartite graph and a graph with maximum degree less than $n$? This is a
question about the size Ramsey number of stars $K_{1,n}$ versus the family of odd cycles.
Faudree proved the conjecture holds when the graph has exactly $2n+1$ vertices (unpublished,
referenced in [Er93]). Disproved in general by Pikhurko [Pi01].

*Reference:* [erdosproblems.com/613](https://www.erdosproblems.com/613)

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.

[Pi01] Pikhurko, O., _Size Ramsey numbers of stars versus 3-chromatic graphs_,
Combinatorica 21 (2001), 403–412.
-/

open scoped Classical
open SimpleGraph

namespace Erdos613

/--
**Erdős Problem 613** (Original conjecture, DISPROVED):

For $n \geq 3$, every graph $G$ with $\binom{2n+1}{2} - \binom{n}{2} - 1$ edges can be written as
the union of a bipartite graph and a graph with maximum degree less than $n$.

This is false, as disproved by Pikhurko [Pi01].
-/
@[category research solved, AMS 5]
theorem erdos_613 : answer(False) ↔ ∀ (n : ℕ), n ≥ 3 →
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
    G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 →
    ∃ (G₁ G₂ : SimpleGraph (Fin m)),
      G₁ ⊔ G₂ = G ∧ G₁.Colorable 2 ∧ G₂.maxDegree < n := by
  sorry

/--
**Erdős Problem 613** (Disproof, Pikhurko [Pi01]):

There exists $n \geq 3$ and a graph $G$ with $\binom{2n+1}{2} - \binom{n}{2} - 1$ edges that
cannot be written as the union of a bipartite graph and a graph with maximum degree less than $n$.
-/
@[category research solved, AMS 5]
theorem erdos_613.variants.disproof :
    ∃ (n : ℕ), n ≥ 3 ∧
    ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
      G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 ∧
      ¬∃ (G₁ G₂ : SimpleGraph (Fin m)),
        G₁ ⊔ G₂ = G ∧ G₁.Colorable 2 ∧ G₂.maxDegree < n := by
  sorry

/--
**Erdős Problem 613** (Faudree's positive result):

For $n \geq 3$, every graph on $2n+1$ vertices with $\binom{2n+1}{2} - \binom{n}{2} - 1$ edges
can be written as the union of a bipartite graph and a graph with maximum degree less than $n$.
That is, the conjecture holds when restricted to graphs with exactly $2n+1$ vertices.
This result is unpublished but referenced in [Er93].
-/
@[category research solved, AMS 5]
theorem erdos_613.variants.faudree : ∀ (n : ℕ), n ≥ 3 →
    ∀ (G : SimpleGraph (Fin (2 * n + 1))),
    -- edge count = C(2n+1, 2) - C(n, 2) - 1 = 3n(n+1)/2 - 1
    G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 →
    ∃ (G₁ G₂ : SimpleGraph (Fin (2 * n + 1))),
      G₁ ⊔ G₂ = G ∧ G₁.Colorable 2 ∧ G₂.maxDegree < n := by
  sorry

end Erdos613
