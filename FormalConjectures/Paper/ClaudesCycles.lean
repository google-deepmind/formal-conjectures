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
# Claude's Cycles

*Reference:* [Claude's Cycles](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)
by *Donald E. Knuth* (2026)

Fix `m ≥ 2`. Consider the directed graph with vertex set `(ZMod m)³`, where from each vertex
`(i, j, k)` there are directed arcs to `(i+1, j, k)`, `(i, j+1, k)`, and `(i, j, k+1)`
(arithmetic mod `m`). The goal is to partition all `3m³` directed arcs into three
edge-disjoint directed Hamiltonian cycles (each of length `m³`).

Knuth describes an explicit construction, found by Claude (Anthropic), that achieves this
decomposition for all odd `m ≥ 3`. The case `m = 2` is known to be impossible [Aub82].
The even case `m > 2` remains open.

## References

- [Knu26] D. E. Knuth, "Claude's Cycles" (2026).
- [Aub82] J. Aubert, B. Schneider, "Graphes orientés indécomposables en circuits hamiltoniens",
  J. Combin. Theory Ser. B 32 (1982), 347–349.
-/

namespace ClaudesCycles

/-- The vertex type: vectors in `(ZMod m)³`. -/
abbrev Vertex (m : ℕ) := Fin 3 → ZMod m

/-- Bump coordinate `b` of vertex `v`: add 1 to the `b`-th component. -/
def bumpAt {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) : Vertex m :=
  Function.update v b (v b + 1)

/-- Adjacency in the cube digraph: `u` is adjacent to `v` if `v` is obtained from `u` by
bumping one coordinate. -/
def cubeAdj {m : ℕ} [NeZero m] (u v : Vertex m) : Prop :=
  ∃ b : Fin 3, bumpAt b u = v

/-- A permutation `σ` on vertices is a directed Hamiltonian cycle of a digraph with adjacency
`adj` if every arc `(v, σ v)` is an edge, `σ` is a single cycle, and `σ` moves every vertex. -/
def IsDirectedHamiltonianCycle {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (σ : Equiv.Perm V) : Prop :=
  (∀ v, adj v (σ v)) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-- The arcs of the cube digraph on `(ZMod m)³` can be decomposed into three directed
Hamiltonian cycles: there exist three permutations, each forming a directed Hamiltonian
cycle, such that every arc `(v, bumpAt b v)` belongs to exactly one cycle. -/
def HasHamiltonianArcDecomposition (m : ℕ) [NeZero m] : Prop :=
  ∃ σ : Fin 3 → Equiv.Perm (Vertex m),
    (∀ c, IsDirectedHamiltonianCycle (cubeAdj (m := m)) (σ c)) ∧
    (∀ v : Vertex m, ∀ b : Fin 3, ∃! c : Fin 3, σ c v = bumpAt b v)

/-- For odd `m > 1`, the cube digraph on `(ZMod m)³` has a Hamiltonian arc decomposition
into three directed cycles [Knu26]. -/
@[category research formally solved using lean4 at
  "https://github.com/kim-em/KnuthClaudeLean", AMS 5]
theorem cube_hamiltonian_arc_decomposition {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    HasHamiltonianArcDecomposition m := by
  sorry

/-- The case `m = 2` is impossible: the cube digraph on `(ZMod 2)³` does not have a
Hamiltonian arc decomposition [Aub82]. -/
@[category research solved, AMS 5]
theorem cube_hamiltonian_arc_decomposition_impossible_m2 :
    ¬ HasHamiltonianArcDecomposition 2 := by
  sorry

/-- For even `m > 2`, it is open whether the cube digraph on `(ZMod m)³` has a Hamiltonian
arc decomposition. -/
@[category research open, AMS 5]
theorem cube_hamiltonian_arc_decomposition_even :
    answer(sorry) ↔ ∀ᵉ (m : ℕ) (_ : NeZero m) (_ : Even m) (_ : 2 < m),
      HasHamiltonianArcDecomposition m := by
  sorry

end ClaudesCycles
