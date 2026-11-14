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
# Kourovka Notebook Problem 20.71

by J. Lauri, communicated by V. Pannone

*Reference:* [The Kourovka Notebook, No. 21, Problem 20.71](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/07/21tkt.pdf)
-/

namespace Kourovka.«20.71»

open SimpleGraph

/-- The cards obtained by deleting `u` and `v` from `G` are isomorphic. -/
def CardIso {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  Nonempty (G.induce {x | x ≠ u} ≃g G.induce {x | x ≠ v})

/-- The vertices `u` and `v` lie in the same orbit of `Aut(G)`. -/
def SameOrbit {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ e : G ≃g G, e u = v

/-- `G` has exactly `k` isomorphism types among its vertex-deleted cards. -/
def HasExactlyCardTypes {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, Function.Surjective c ∧
    ∀ u v, CardIso G u v ↔ c u = c v

/-- The action of `Aut(G)` on vertices has exactly `k` orbits. -/
def HasExactlyVertexOrbits {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, Function.Surjective c ∧
    ∀ u v, SameOrbit G u v ↔ c u = c v

/--
Can a connected graph with exactly `2` isomorphism types of cards have more
than `2` orbits of its automorphism group on the vertex set? An exhaustive
search shows any example has at least `12` vertices.
-/
@[category research open, AMS 5 20]
theorem kourovka.«20.71».variants.k2 : answer(sorry) ↔
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected ∧
      HasExactlyCardTypes G 2 ∧ ∃ m, 2 < m ∧ HasExactlyVertexOrbits G m := by
  sorry

/--
Can a connected graph with exactly `3` isomorphism types of cards have more
than `3` orbits of its automorphism group on the vertex set? An exhaustive
search shows any example has at least `12` vertices.
-/
@[category research open, AMS 5 20]
theorem kourovka.«20.71».variants.k3 : answer(sorry) ↔
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected ∧
      HasExactlyCardTypes G 3 ∧ ∃ m, 3 < m ∧ HasExactlyVertexOrbits G m := by
  sorry

/--
The `k = 4` case of Kourovka Notebook Problem 20.71 has an affirmative
answer: there is a connected graph with exactly four card types and more
than four automorphism orbits.

The linked certificate verifies a graph on nine vertices (graph6 `HCpbdgy`)
with exactly four card types and exactly five vertex orbits; by exhaustive
search it is of minimum order and unique at that order up to
complementation, and no example of order `10` exists.
-/
@[category research solved, AMS 5 20,
  formal_proof using lean4 at
    "https://github.com/infinityscroll/kourovka-20-71/blob/d6c6dd30105b7dc362597ef77835f31209e6bbae/Kourovka2071.lean"]
theorem kourovka.«20.71».variants.k4 : answer(True) ↔
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected ∧
      HasExactlyCardTypes G 4 ∧ ∃ m, 4 < m ∧ HasExactlyVertexOrbits G m := by
  sorry

end Kourovka.«20.71»
