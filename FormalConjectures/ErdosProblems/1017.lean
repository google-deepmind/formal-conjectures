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
# Erdős Problem 1017

*Reference:* [erdosproblems.com/1017](https://www.erdosproblems.com/1017)

Let $f(n,k)$ be such that every graph on $n$ vertices and $k$ edges can be
partitioned into at most $f(n,k)$ edge-disjoint complete graphs. Estimate
$f(n,k)$ for $k > n^2/4$.

The function $f(n,k)$ is sometimes called the clique partition number.

Erdős, Goodman, and Pósa [EGP66] proved that $f(n,k) \le \lfloor n^2/4 \rfloor$ for all $k$
(and in fact edges and triangles suffice), which is best possible in general,
as witnessed by a complete bipartite graph. Erdős [Er71] asks whether this
bound can be sharpened when $k > n^2/4$.

[EGP66] Erdős, P., Goodman, A. W., and Pósa, L., _The representation of a graph by set
intersections_. Canadian Journal of Mathematics 18 (1966), 106-112.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open SimpleGraph Finset Filter

namespace Erdos1017

/--
Erdős Problem 1017 [Er71]:

Erdős asks whether the clique partition number $f(n,k)$ can be improved
below $\lfloor n^2/4 \rfloor$ when the number of edges $k$ exceeds $n^2/4$.
-/
@[category research open, AMS 5]
theorem erdos_1017 : answer(sorry) ↔
    ∀ᶠ n in atTop,
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card > n ^ 2 / 4 →
          ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
            k < n ^ 2 / 4 ∧
            (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
            (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
            (∀ i : Fin k, ∃ (S : Finset (Fin n)),
              G.IsClique (↑S : Set (Fin n)) ∧
              parts i = S.offDiag.image (Quot.mk _)) := by
  sorry

/--
Erdős–Goodman–Pósa theorem [EGP66]:

Every simple graph on $n$ vertices can be decomposed into at most
$\lfloor n^2/4 \rfloor$ edge-disjoint complete subgraphs.
-/
@[category research solved, AMS 5]
theorem erdos_1017.variants.erdos_goodman_posa :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
        k ≤ n ^ 2 / 4 ∧
        (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
        (∀ i : Fin k, ∃ (S : Finset (Fin n)),
          G.IsClique (↑S : Set (Fin n)) ∧
          parts i = S.offDiag.image (Quot.mk _)) := by
  sorry

end Erdos1017
