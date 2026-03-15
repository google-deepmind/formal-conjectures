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
# Erdős Problem 1007

*Reference:* [erdosproblems.com/1007](https://www.erdosproblems.com/1007)

The dimension of a graph $G$ is the minimal $n$ such that $G$ can be embedded in
$\mathbb{R}^n$ such that every edge of $G$ is a unit line segment (adjacent vertices are at
Euclidean distance exactly $1$, and non-adjacent vertices are not). This notion
was defined by Erdős, Harary, and Tutte. The problem was posed by Erdős to
Soifer in January 1992.

[So09e] Soifer, A., *The Mathematical Coloring Book*, Springer, 2009.

[Ho13] House, R. F., *A 4-dimensional graph has at least 9 edges*.
Discrete Mathematics **313** (2013), 1783–1789.

[ChNo16] Chaffee, J. and Noble, M., *Dimension 4 and dimension 5 graphs with
minimum edge set*. Australasian Journal of Combinatorics **64** (2016), 327–333.
-/

open SimpleGraph

namespace Erdos1007

/-- A unit-distance representation of a simple graph $G$ in $\mathbb{R}^n$: an injective map
from vertices to Euclidean $n$-space such that adjacency is equivalent to
distance exactly $1$. Injectivity is needed to prevent collapsing distinct
non-adjacent vertices to the same point (the adjacency biconditional alone does
not rule this out). -/
def IsUnitDistRep {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (f : V → EuclideanSpace ℝ (Fin n)) : Prop :=
  Function.Injective f ∧
  ∀ u v, G.Adj u v ↔ dist (f u) (f v) = 1

/-- A graph admits a unit-distance representation in $\mathbb{R}^n$. -/
def HasUnitDistRep {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), IsUnitDistRep G n f

/--
Erdős Problem 1007 [So09e]:

The smallest number of edges in a graph of dimension exactly $4$ is $9$, where the
dimension of a graph is the minimal $n$ for a unit-distance representation in $\mathbb{R}^n$.

This is achieved uniquely by $K_{3,3}$. Proved by House [Ho13], with an alternative
proof by Chaffee and Noble [ChNo16].
-/
@[category research solved, AMS 5 51]
theorem erdos_1007 :
    -- There exists a graph of dimension exactly 4 with 9 edges
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
       (_ : DecidableRel G.Adj),
       HasUnitDistRep G 4 ∧ ¬HasUnitDistRep G 3 ∧ G.edgeFinset.card = 9) ∧
    -- Every graph of dimension exactly 4 has at least 9 edges
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
       [DecidableRel G.Adj],
       HasUnitDistRep G 4 → ¬HasUnitDistRep G 3 → 9 ≤ G.edgeFinset.card) := by
  sorry

/--
Uniqueness variant of Erdős Problem 1007 [Ho13]:

Any graph of dimension exactly $4$ with exactly $9$ edges is isomorphic to $K_{3,3}$.
-/
@[category research solved, AMS 5 51]
theorem erdos_1007_unique (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h4 : HasUnitDistRep G 4) (h3 : ¬HasUnitDistRep G 3)
    (hedge : G.edgeFinset.card = 9) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  sorry

/--
Dimension-5 analogue of Erdős Problem 1007 [ChNo16]:

The smallest number of edges in a graph of dimension exactly $5$ is $15$.
-/
@[category research solved, AMS 5 51]
theorem erdos_1007_dim5 :
    -- There exists a graph of dimension exactly 5 with 15 edges
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
       (_ : DecidableRel G.Adj),
       HasUnitDistRep G 5 ∧ ¬HasUnitDistRep G 4 ∧ G.edgeFinset.card = 15) ∧
    -- Every graph of dimension exactly 5 has at least 15 edges
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
       [DecidableRel G.Adj],
       HasUnitDistRep G 5 → ¬HasUnitDistRep G 4 → 15 ≤ G.edgeFinset.card) := by
  sorry

end Erdos1007
