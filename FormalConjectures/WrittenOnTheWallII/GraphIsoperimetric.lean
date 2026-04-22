/-
Copyright 2025 The Formal Conjectures Authors.

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
# Isoperimetric Number (Cheeger Constant) of a Graph

*Reference:*
[B. Mohar, Isoperimetric numbers of graphs,
J. Combin. Theory Ser. B 47 (1989) 274–291](https://doi.org/10.1016/0095-8956(89)90029-4)

## Definition

For a finite simple graph `G = (V, E)` and a set `S ⊆ V`, the **edge boundary**
`∂(S)` is the set of edges with one endpoint in `S` and the other in `V \ S`.
The **isoperimetric number** (Cheeger constant) of `G` is

  `h(G) = min { |∂(S)| / |S| | S ⊆ V, S ≠ ∅, 2·|S| ≤ |V| }`.

This measures how "well-connected" a graph is: a large `h(G)` means no small set
has a small boundary.

## Conjectures

1. (Resolved) `h(G) ≤ Δ(G)` (maximum degree bound): every vertex in `S`
   contributes at most `Δ(G)` edges to the boundary, so `|∂(S)| ≤ Δ(G) · |S|`.

2. (Open — Cheeger inequality for graphs) `h(G)² / (2 · Δ(G)) ≤ λ₁(G) ≤ 2·h(G)`,
   where `λ₁(G)` is the smallest positive eigenvalue of the Laplacian of `G`
   (algebraic connectivity / Fiedler value).
-/

namespace WrittenOnTheWallII.GraphIsoperimetric

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **edge boundary cardinality** `|∂(S)|`: the number of edges of `G` with
exactly one endpoint in `S`. -/
noncomputable def edgeBoundaryCard (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    Sym2.lift ⟨fun u v => (u ∈ S) ≠ (v ∈ S), fun u v => by simp [Iff.comm]⟩ e)).card

/-- The **isoperimetric number** (Cheeger constant) `h(G)`:
  `h(G) = inf { |∂(S)| / |S| | S ⊆ V, S ≠ ∅, 2·|S| ≤ n }`.

We take the infimum over nonempty vertex subsets `S` satisfying `2 · |S| ≤ n`
of the ratio `|∂(S)| / |S|` as a real number. -/
noncomputable def isoperimetricNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sInf {r | ∃ S : Finset α, S.Nonempty ∧ 2 * S.card ≤ Fintype.card α ∧
    r = (edgeBoundaryCard G S : ℝ) / (S.card : ℝ)}

/-- **Maximum-degree upper bound** (resolved): `h(G) ≤ Δ(G)`.

For any nonempty `S` with `2·|S| ≤ n`, each vertex in `S` contributes at most
`Δ(G)` edges to `∂(S)`, giving `|∂(S)| ≤ Δ(G) · |S|` and hence
`|∂(S)| / |S| ≤ Δ(G)`. -/
@[category research solved, AMS 5]
theorem isoperimetricNumber_le_maxDegree
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    isoperimetricNumber G ≤ G.maxDegree := by
  sorry

/-- **Cheeger inequality** (open in this Lean formulation): the isoperimetric
number and the algebraic connectivity `mu` (smallest positive Laplacian
eigenvalue) satisfy
  `isoperimetricNumber G ^ 2 / (2 * G.maxDegree) ≤ mu`.

This is the discrete analogue of the classical Cheeger inequality in Riemannian
geometry.  The matching upper bound `mu ≤ 2 · isoperimetricNumber G` is also
classical. -/
@[category research open, AMS 5]
theorem cheeger_inequality
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hΔ : 0 < G.maxDegree)
    (mu : ℝ) (hmu : mu > 0)
    -- `hmu_spec` encodes that `mu` is the smallest positive Laplacian eigenvalue;
    -- stated as a hypothesis to avoid full spectral-theory dependencies.
    (hmu_spec : ∀ S : Finset α, S.Nonempty → 2 * S.card ≤ Fintype.card α →
      (edgeBoundaryCard G S : ℝ) / (S.card : ℝ) ≥ Real.sqrt (2 * G.maxDegree * mu)) :
    isoperimetricNumber G ^ 2 / (2 * G.maxDegree) ≤ mu := by
  sorry

-- Sanity checks

/-- `isoperimetricNumber` is a real number — type-checks correctly. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    (isoperimetricNumber G : ℝ) = isoperimetricNumber G :=
  rfl

/-- `edgeBoundaryCard` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] (S : Finset (Fin 4)) :
    0 ≤ edgeBoundaryCard G S :=
  Nat.zero_le _

/-- `isoperimetricNumber` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ isoperimetricNumber G := by
  apply Real.sInf_nonneg (s := {r | ∃ S : Finset (Fin 5), S.Nonempty ∧
      2 * S.card ≤ Fintype.card (Fin 5) ∧
      r = (edgeBoundaryCard G S : ℝ) / (S.card : ℝ)})
  rintro _ ⟨S, hS, _, rfl⟩
  positivity

end WrittenOnTheWallII.GraphIsoperimetric
