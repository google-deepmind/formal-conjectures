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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.EdgeColouring

@[expose] public section

/-!
# Ramsey-type properties of graph pairs

The Erdős–Hajnal "exceptional pair" trio of predicates:

- `HasFiniteRamseyProperty G₁ G₂` — for every `n ≥ 1` there is a `G₁`-free graph `H` such
  that every `n`-edge-colouring of `H` contains a monochromatic `G₂`.
- `HasCountableRamseyEscape G₁ G₂` — every `G₁`-free graph `H` admits a countable
  edge-colouring with every colour class `G₂`-free.
- `IsErdosHajnalExceptional G₁ G₂` — the conjunction of both.

These were introduced for Erdős Problem 596 but are reusable for Problem 595 and other
Ramsey-type questions; we factor them out per mo271's review.

It also defines the two-colour graph Ramsey number `graphRamsey G H` and the notion of a
**Ramsey size linear** graph `IsRamseySizeLinear G` of Erdős, Faudree, Rousseau and Schelp.

## References

* Erdős, Faudree, Rousseau and Schelp, *Ramsey size linear graphs*,
  Combin. Probab. Comput. 2 (1993), 389–399.
-/

namespace SimpleGraph

/-- The **finite Ramsey property** for the pair $(G_1, G_2)$: for every $n \geq 1$, there
exists a $G_1$-free graph `H` on some vertex type in `Type` (universe 0) such that every
`n`-edge-colouring of `H` contains a monochromatic copy of `G_2`. -/
def HasFiniteRamseyProperty {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∃ (V : Type) (H : SimpleGraph V),
    G₁.Free H ∧
    ∀ (c : Fin n → SimpleGraph V), H.IsEdgeColouring c →
      ∃ i, G₂ ⊑ c i

/-- The **countable Ramsey escape property** for the pair $(G_1, G_2)$: every $G_1$-free
graph `H` on a `Type`-valued vertex type has a countable edge-colouring in which every
colour class is $G_2$-free. -/
def HasCountableRamseyEscape {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ (W : Type) (H : SimpleGraph W),
    G₁.Free H →
    ∃ (d : ℕ → SimpleGraph W),
      H.IsEdgeColouring d ∧ ∀ j, G₂.Free (d j)

/-- A pair $(G_1, G_2)$ is **Erdős–Hajnal exceptional** if it has both the finite Ramsey
property and the countable Ramsey escape property. -/
def IsErdosHajnalExceptional {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  HasFiniteRamseyProperty G₁ G₂ ∧ HasCountableRamseyEscape G₁ G₂

/--
The two-color Ramsey number `graphRamsey G H` is the minimum number of vertices `n`
such that every 2-coloring of the edges of the complete graph on `n` vertices contains
a copy of `G` in the first color or a copy of `H` in the second color.

A 2-coloring of the complete graph on `Fin n` is represented by a graph `C` (the edges of the
first color) and its complement `Cᶜ` (the edges of the second color).
-/
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

/-- The diagonal graph Ramsey number `R(G, G)`. -/
noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphRamsey G G

/-- The classical two-color Ramsey number `R(k, l) = R(K_k, K_l)`. -/
noncomputable def classicalRamsey (k l : ℕ) : ℕ :=
  graphRamsey (completeGraph (Fin k)) (completeGraph (Fin l))

/-- The diagonal classical Ramsey number `R(k) = R(K_k, K_k)`. -/
noncomputable def diagonalRamsey (k : ℕ) : ℕ :=
  classicalRamsey k k

/--
A graph `G` is **Ramsey size linear** if there exists a constant `c > 0` such that
for all graphs `H` with `m` edges and no isolated vertices, the Ramsey number satisfies
`R(G, H) ≤ c · m`.

Note that this is about the (vertex) Ramsey number `graphRamsey G H`, not the size Ramsey
number `sizeRamsey G H`.
-/
def IsRamseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (graphRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

end SimpleGraph
