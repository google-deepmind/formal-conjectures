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
# Erdős Problem 1006

*Reference:* [erdosproblems.com/1006](https://www.erdosproblems.com/1006)

Let $G$ be a graph with girth $> 4$. Can the edges of $G$ always be oriented so that the
resulting directed graph is acyclic, and reversing any single edge also leaves it acyclic?
Originally due to Ore (cited in [Er71]). Ore gave a counterexample with girth 4;
Gallai observed the Grötzsch graph also fails. Disproved by Nešetřil and Rödl [NeRo78b].

[Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969), pp. 97–109, 1971.

[Er76b] Erdős, P., *Problems in combinatorial and graph theory* (1976).

[NeRo78b] Nešetřil, J. and Rödl, V., *On a probabilistic graph-theoretical method*.
Proceedings of the American Mathematical Society, pp. 417–421, 1978.
-/

open SimpleGraph

namespace Erdos1006

variable {V : Type*}

/-- An orientation of a simple graph $G$: a relation `dir` on $V$ such that for each
edge $\{u, v\}$, exactly one of `dir u v` or `dir v u` holds, and `dir` only
relates adjacent vertices. -/
structure Orientation (G : SimpleGraph V) where
  dir : V → V → Prop
  adj_of_dir : ∀ u v, dir u v → G.Adj u v
  dir_of_adj : ∀ u v, G.Adj u v → dir u v ∨ dir v u
  antisymm : ∀ u v, dir u v → ¬dir v u

/-- An orientation is acyclic if the transitive closure of its direction relation
is irreflexive (equivalently, there are no directed cycles). -/
def Orientation.IsAcyclic {G : SimpleGraph V} (o : Orientation G) : Prop :=
  ∀ v, ¬Relation.TransGen o.dir v v

/-- The relation obtained by flipping one directed edge $(a \to b)$ to $(b \to a)$,
keeping all other directed edges the same. -/
def flipDir (dir : V → V → Prop) (a b : V) : V → V → Prop :=
  fun u v => (u = b ∧ v = a ∧ dir a b) ∨ (dir u v ∧ ¬(u = a ∧ v = b))

/-- An orientation is robustly acyclic if it is acyclic and reversing any
single directed edge also yields an acyclic relation. -/
def Orientation.IsRobustlyAcyclic {G : SimpleGraph V} (o : Orientation G) : Prop :=
  o.IsAcyclic ∧
  ∀ a b, o.dir a b →
    ∀ v, ¬Relation.TransGen (flipDir o.dir a b) v v

/--
Erdős Problem 1006 (disproved) [Er71][Er76b]:

Let $G$ be a graph with girth $> 4$ (i.e., $G$ contains no cycles of length $3$ or $4$).
Can the edges of $G$ always be directed such that there is no directed cycle, and
reversing the direction of any edge also creates no directed cycle?

This was disproved by Nešetřil and Rödl [NeRo78b], who proved that for every
integer $g$, there is a graph $G$ with girth $g$ such that every orientation of $G$ either
contains a directed cycle or contains a cycle obtained by reversing one edge.
-/
@[category research solved, AMS 5]
theorem erdos_1006 : answer(False) ↔
    ∀ (V : Type*) (G : SimpleGraph V), 5 ≤ G.egirth →
    ∃ o : Orientation G, o.IsRobustlyAcyclic := by
  sorry

/--
Variant of Erdős Problem 1006 (Nešetřil–Rödl [NeRo78b]):

For every integer $g$, there exists a graph $G$ with girth $\ge g$ such that no orientation of
$G$ is robustly acyclic. This strengthens the original problem by showing that high girth alone
never suffices.
-/
@[category research solved, AMS 5]
theorem erdos_1006_arbitrary_girth : answer(False) ↔
    ∀ (g : ℕ) (V : Type*) (G : SimpleGraph V), g ≤ G.egirth →
    ∃ o : Orientation G, o.IsRobustlyAcyclic := by
  sorry

end Erdos1006
