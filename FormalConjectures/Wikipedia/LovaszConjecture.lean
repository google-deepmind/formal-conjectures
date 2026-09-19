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
# Lovász's conjecture on Hamiltonian paths in vertex-transitive graphs (1970)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Lov%C3%A1sz_conjecture)
* [Lo70] Lovász, L. (1970). Problem 11, in *Combinatorial Structures and their Applications*
  (Proc. Calgary Internat. Conf. 1969), Gordon and Breach, p. 497.
* [Ba79] Babai, L. (1979). "Long cycles in vertex-transitive graphs." *J. Graph Theory* 3,
  pp. 301--304.
* [CHM14] Christofides, D., Hladký, J. and Máthé, A. (2014). "Hamilton cycles in dense
  vertex-transitive graphs." *J. Combin. Theory Ser. B* 109, pp. 34--72.
  [arXiv:1008.2193](https://arxiv.org/abs/1008.2193)
* [KM09] Kutnar, K. and Marušič, D. (2009). "Hamilton cycles and paths in vertex-transitive
  graphs — current directions." *Discrete Math.* 309, pp. 5491--5500.
-/

open SimpleGraph

namespace LovaszConjecture

variable {V : Type*}

/-- A graph is **vertex-transitive** if its automorphism group acts transitively on the
vertices: any vertex can be mapped to any other by a graph automorphism. -/
def IsVertexTransitive (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- `G` has a **Hamiltonian path**: a walk visiting every vertex exactly once. -/
def HasHamiltonianPath [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian

/--
**Lovász's conjecture (1970).**

Every finite connected vertex-transitive graph has a Hamiltonian path.
-/
@[category research open, AMS 5]
theorem lovasz_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → IsVertexTransitive G → HasHamiltonianPath G := by
  sorry

/--
**Babai (1979): long cycles in vertex-transitive graphs.**

Every finite connected vertex-transitive graph on $n \ge 3$ vertices contains a cycle of length
at least $\sqrt{3n}$.

*Reference:* [Ba79].
-/
@[category research solved, AMS 5]
theorem lovasz_conjecture.variants.babai
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ) := by
  sorry

/--
**Christofides–Hladký–Máthé (2014): the dense case.**

For every $\varepsilon > 0$ there is $n_0$ such that every connected vertex-transitive graph on
$n \ge n_0$ vertices with minimum degree at least $\varepsilon n$ has a Hamiltonian cycle (and
hence a Hamiltonian path).

*Reference:* [CHM14].
-/
@[category research solved, AMS 5]
theorem lovasz_conjecture.variants.dense :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      G.Connected → IsVertexTransitive G → ε * Fintype.card V ≤ G.minDegree →
      HasHamiltonianPath G := by
  sorry

/-- Complete graphs are vertex-transitive: any transposition is an automorphism. -/
@[category API, AMS 5]
lemma isVertexTransitive_top [DecidableEq V] : IsVertexTransitive (⊤ : SimpleGraph V) :=
  fun u v => ⟨⟨Equiv.swap u v, by simp [top_adj]⟩, Equiv.swap_apply_left u v⟩

/-- Empty graphs are vertex-transitive. -/
@[category API, AMS 5]
lemma isVertexTransitive_bot [DecidableEq V] : IsVertexTransitive (⊥ : SimpleGraph V) :=
  fun u v => ⟨⟨Equiv.swap u v, by simp⟩, Equiv.swap_apply_left u v⟩

/--
**Graphs on at most one vertex.**

A connected graph on a single vertex trivially has a Hamiltonian path (the trivial walk).
-/
@[category test, AMS 5]
theorem lovasz_conjecture.variants.subsingleton [DecidableEq V] [Subsingleton V] [Nonempty V]
    (G : SimpleGraph V) : HasHamiltonianPath G :=
  ⟨Classical.arbitrary V, Classical.arbitrary V, Walk.nil,
    Walk.IsHamiltonian.of_subsingleton (p := (Walk.nil : G.Walk _ _))⟩

end LovaszConjecture
