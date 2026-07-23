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
# Erdős Problem 1007

*References:*
- [erdosproblems.com/1007](https://www.erdosproblems.com/1007)
- [ChNo16] Chaffee, Joe and Noble, Matt, *Dimension 4 and dimension 5 graphs with minimum edge
  set*. Australas. J. Combin. (2016), 327-333.
- [Ho13] House, Roger F., *A 4-dimensional graph has at least 9 edges*. Discrete Math. (2013),
  1783-1789.
-/

namespace Erdos1007

open scoped EuclideanGeometry

variable {V : Type*}

/--
A graph `G` can be embedded in `ℝ^n` with every edge a unit line segment if there is an
injective map from the vertices of `G` to `ℝ^n` sending any two adjacent vertices to a pair of
points at distance `1`.
-/
def UnitDistanceEmbeddable (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → ℝ^n, Function.Injective f ∧ ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

/--
`G` has dimension `n`, that is, `n` is the minimal natural number such that `G` can be embedded
in `ℝ^n` with every edge of `G` a unit line segment.
-/
def HasDimension (G : SimpleGraph V) (n : ℕ) : Prop :=
  IsLeast {m | UnitDistanceEmbeddable G m} n

/-- The complete tripartite graph $K_{1,3,3}$. -/
abbrev K133 := SimpleGraph.completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)

/--
The dimension of a graph $G$ is the minimal $n$ such that $G$ can be embedded in $\mathbb{R}^n$
such that every edge of $G$ is a unit line segment.

What is the smallest number of edges in a graph with dimension $4$?

The smallest number of edges is $9$, achieved solely by $K_{3,3}$, proved by House [Ho13]. An
alternative proof was given by Chaffee and Noble [ChNo16], who also prove that the smallest
number of edges in a graph of dimension $5$ is $15$ (achieved by $K_6$ and $K_{1,3,3}$).
-/
@[category research solved, AMS 5 52]
theorem erdos_1007 :
    IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), HasDimension G 4 ∧ G.edgeSet.ncard = m}
      answer(sorry) := by
  sorry

/--
The smallest number of edges in a graph of dimension $4$ is $9$.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1007.lean"]
theorem erdos_1007.variants.dimension_four :
    IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), HasDimension G 4 ∧ G.edgeSet.ncard = m}
      9 := by
  sorry

/--
The smallest number of edges in a graph of dimension $4$ is achieved solely by $K_{3,3}$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1007.variants.dimension_four_extremal (n : ℕ) (G : SimpleGraph (Fin n))
    (hdim : HasDimension G 4) (hcard : G.edgeSet.ncard = 9)
    (hdeg : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  sorry

/--
The smallest number of edges in a graph of dimension $5$ is $15$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1007.variants.dimension_five :
    IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), HasDimension G 5 ∧ G.edgeSet.ncard = m}
      15 := by
  sorry

/--
The smallest number of edges in a graph of dimension $5$ is achieved by $K_6$ and $K_{1,3,3}$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1007.variants.dimension_five_extremal :
    (HasDimension (SimpleGraph.completeGraph (Fin 6)) 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (HasDimension K133 5 ∧ K133.edgeSet.ncard = 15) := by
  sorry

end Erdos1007
