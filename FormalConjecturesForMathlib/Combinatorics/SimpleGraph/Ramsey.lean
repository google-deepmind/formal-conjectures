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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Nat.Lattice

@[expose] public section

/-!
# Graph Ramsey Numbers

This file defines the classical 2-color graph Ramsey number `R(k, l)`, the diagonal graph
Ramsey number `R(H)` for a given graph `H`, and the diagonal Ramsey number `R(k)`.
-/

namespace SimpleGraph

/--
`IsGraphRamsey n k l` means that for every simple graph `G` on `n` vertices, either
- `G` contains a clique of size `k`, or
- the complement graph `Gᶜ` contains a clique of size `l` (equivalently, `G` contains an
  independent set of size `l`).
-/
def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

/-- Monotonicity in the number of vertices. -/
theorem IsGraphRamsey.succ (n k l : ℕ) :
    IsGraphRamsey n k l → IsGraphRamsey (n + 1) k l := by
  intro h G
  -- Restrict to the induced subgraph on the first `n` vertices.
  let H : SimpleGraph (Fin n) := G.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))
  have emb : H ↪g G := SimpleGraph.Embedding.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) G
  have embc : (Hᶜ) ↪g (Gᶜ) := (SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun emb
  rintro ⟨hG, hGc⟩
  have hH : H.CliqueFree k := SimpleGraph.CliqueFree.comap (f := emb) (n := k) hG
  have hHc : (Hᶜ).CliqueFree l := SimpleGraph.CliqueFree.comap (f := embc) (n := l) hGc
  exact (h H) ⟨hH, hHc⟩

/-- Symmetry in the clique / independent set sizes. -/
theorem IsGraphRamsey.symm (n k l : ℕ) :
    IsGraphRamsey n k l ↔ IsGraphRamsey n l k := by
  constructor <;> intro h G
  · simpa [IsGraphRamsey, and_comm, and_left_comm, and_assoc] using h (Gᶜ)
  · simpa [IsGraphRamsey, and_comm, and_left_comm, and_assoc] using h (Gᶜ)

/--
The (graph) Ramsey number `R(k, l)` is the least natural number `n` such that
`IsGraphRamsey n k l` holds.
-/
noncomputable def graphRamseyNumber (k l : ℕ) : ℕ :=
  sInf {n : ℕ | IsGraphRamsey n k l}

/-- The diagonal graph Ramsey number `R(H)`: the minimum `N` such that every simple
graph `G` on `N` vertices either contains a copy of `H` as a subgraph or its
complement contains a copy of `H`. -/
noncomputable def ramseyNumber {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    H.IsContained G ∨ H.IsContained Gᶜ}

/-- The classical diagonal Ramsey number `R(k) := R(K_k, K_k)`. -/
noncomputable def diagRamseyNumber (k : ℕ) : ℕ :=
  ramseyNumber (⊤ : SimpleGraph (Fin k))

/-- The two Ramsey number definitions agree on the diagonal:
`graphRamseyNumber k k = diagRamseyNumber k`. -/
theorem graphRamseyNumber_self_eq_diagRamseyNumber (k : ℕ) :
    graphRamseyNumber k k = diagRamseyNumber k := by
  sorry

/-- `IsGraphRamsey n 2 l` holds iff `l ≤ n`: any graph on `n ≥ l` vertices
either has an edge (2-clique) or is edgeless (complement contains `l`-clique). -/
theorem isGraphRamsey_two_iff {n l : ℕ} :
    IsGraphRamsey n 2 l ↔ l ≤ n := by
  sorry

/-- `R(2, l) = l` for all `l`. -/
theorem graphRamseyNumber_two (l : ℕ) : graphRamseyNumber 2 l = l := by
  sorry

end SimpleGraph
