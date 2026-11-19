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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 638

*References:*
- [erdosproblems.com/638](https://www.erdosproblems.com/638)
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81-85.
- [Sa26] Saturnino, Brian, *A counterexample to a hereditary triangle Ramsey compactness
  problem* (2026).
- [SF26] Star Fleet Math, *Erdős Problem 638: No — Even for the Hereditary Reading* (2026).
-/

@[expose] public section

namespace Erdos638

/-- Membership in a finite graph family is independent of the vertex labelling. -/
def IsoClosed (S : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ m n (H : SimpleGraph (Fin m)) (K : SimpleGraph (Fin n)),
    Nonempty (H ≃g K) → H ∈ S m → K ∈ S n

/-- The family contains every ordinary finite subgraph of each member. -/
def SubgraphClosed (S : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ m n (H : SimpleGraph (Fin m)) (K : SimpleGraph (Fin n)),
    H.IsContained K → K ∈ S n → H ∈ S m

/-- Every ordinary finite subgraph of the host belongs to the family, up to relabelling. -/
def FiniteSubgraphsIn (S : (n : ℕ) → Set (SimpleGraph (Fin n)))
    {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n (H : SimpleGraph (Fin n)), H.IsContained G → H ∈ S n

/-- Every edge colouring with colours in `C` contains a monochromatic triangle. -/
def ArrowsTriangle {V : Type*} (G : SimpleGraph V) (C : Type*) : Prop :=
  ∀ c : G.EdgeLabeling C,
    ∃ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z),
      c.get x y hxy = c.get y z hyz ∧ c.get y z hyz = c.get x z hxz

/-- The family has a triangle-Ramsey member for each positive finite number of colours. -/
def FiniteRamseyRich (S : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ r : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ S n ∧ ArrowsTriangle G (Fin (r + 1))

/--
Let $S$ be a family of finite graphs such that for every $n$ there is some $G_n\in S$
such that if the edges of $G_n$ are coloured with $n$ colours then there is a monochromatic
triangle.

Is it true that for every infinite cardinal $\aleph$ there is a graph $G$ of which every
finite subgraph is in $S$ and if the edges of $G$ are coloured with $\aleph$ many colours
then there is a monochromatic triangle.

The literal answer is no. A family consisting of graphs containing a triangle satisfies
all finite-colour hypotheses but excludes the one-vertex subgraph of every nonempty host.
The linked formalization proves this counterexample [SF26]. Infinite colour cardinals are
represented by infinite colour types; the host may live in the next universe.
-/
@[category research solved, question, AMS 3 5, formal_proof using lean4 at
  "https://github.com/AItoBit/formal-conjectures/blob/3b1d20570f88d7d0d7ad4271db811c2b22f7501f/proofs/erdos638/Bridge638.lean"]
theorem erdos_638.{u} :
    ¬ ∀ S : (n : ℕ) → Set (SimpleGraph (Fin n)), IsoClosed S → FiniteRamseyRich S →
      ∀ C : Type u, Infinite C → ∃ (V : Type (u + 1)) (G : SimpleGraph V),
        FiniteSubgraphsIn S G ∧ ArrowsTriangle G C := by
  sorry

/--
Does the assertion in Erdős Problem 638 hold when $S$ is closed under taking ordinary
finite subgraphs?

This also has a negative answer. Saturnino [Sa26] gives a counterexample construction;
Star Fleet Math [SF26] supplies a complete Lean proof, including the sparse finite Ramsey
input. The closure condition permits deletion of both vertices and edges.
-/
@[category research solved, question, AMS 3 5, formal_proof using lean4 at
  "https://github.com/AItoBit/formal-conjectures/blob/3b1d20570f88d7d0d7ad4271db811c2b22f7501f/proofs/erdos638/Bridge638.lean"]
theorem erdos_638.variants.subgraph_closed.{u} :
    ¬ ∀ S : (n : ℕ) → Set (SimpleGraph (Fin n)), SubgraphClosed S → FiniteRamseyRich S →
      ∀ C : Type u, Infinite C → ∃ (V : Type (u + 1)) (G : SimpleGraph V),
        FiniteSubgraphsIn S G ∧ ArrowsTriangle G C := by
  sorry

end Erdos638
