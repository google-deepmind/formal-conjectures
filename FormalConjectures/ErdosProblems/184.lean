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
# Erdős Problem 184

*Reference:* [erdosproblems.com/184](https://www.erdosproblems.com/184)

Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles
and edges.

Conjectured by Erdős and Gallai [EGP66], who proved that $O(n \log n)$ many cycles
and edges suffice. The best bound is due to Bucić and Montgomery [BM22], who
prove that $O(n \log^* n)$ suffice. Conlon, Fox, and Sudakov [CFS14] proved that
$O_\varepsilon(n)$ cycles and edges suffice if $G$ has minimum degree at least
$\varepsilon n$. The graph $K_{3,n-3}$ shows that at least $(1+c)n$ parts are
needed for some constant $c > 0$.

See also Problem 583 (decomposition into paths) and Problem 1017 (decomposition
into complete graphs).

[EGP66] Erdős, P. and Gallai, T., _On the maximal number of vertices representing
the edges of a graph_, 1966.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial
analysis_. Combinatorial Mathematics and its Applications (1971), 97-109.

[BM22] Bucić, M. and Montgomery, R., _Towards the Erdős-Gallai cycle decomposition
conjecture_. arXiv:2211.07689 (2022).

[CFS14] Conlon, D., Fox, J., and Sudakov, B., _Cycle packing_. Random Structures
Algorithms (2014), 608-626.
-/

open SimpleGraph

namespace Erdos184

/--
Erdős Problem 184 (Erdős-Gallai conjecture) [EGP66, Er71, Er76, Er81, Er83b]:

There exists a constant $C > 0$ such that for every $n$ and every simple graph $G$ on
$n$ vertices, the edge set of $G$ can be partitioned into at most $C \cdot n$ parts, where
each part is either a single edge or the edge set of a cycle in $G$.
-/
@[category research open, AMS 5]
theorem erdos_184 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
        (k : ℝ) ≤ C * (n : ℝ) ∧
        (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
        (∀ i : Fin k,
          (∃ e, parts i = {e}) ∨
          (∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ w.edges.toFinset = parts i)) := by
  sorry

end Erdos184
