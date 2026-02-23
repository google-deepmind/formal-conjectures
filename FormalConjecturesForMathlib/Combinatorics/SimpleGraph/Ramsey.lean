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
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Term

/-!
# Graph Ramsey Number

This file defines the graph Ramsey number for simple graphs.

## Definitions

* `graphRamseyNum` - The n-ary graph Ramsey number `R(H₀, H₁, ..., Hₙ₋₁)`.
* `Ramsey` - The 2-ary graph Ramsey number `R(G, H)` via the complement formulation.

## Main Results

* `SimpleGraph.Ramsey.le` - If the complement Ramsey property holds at `N`, then `Ramsey G H ≤ N`.

## Main Definition

The graph Ramsey number `R(H₀, H₁, ..., Hₙ₋₁)` is the smallest natural number `N` such that
any edge-coloring of the complete graph `K_N` with `n` colors contains a monochromatic
copy of `Hᵢ` in color `i` for some `i`.

Equivalently, for any partition of `K_N`'s edges into `n` subgraphs `c 0, c 1, ..., c (n-1)`,
there exists `i` such that `Hᵢ` is contained in `c i`.

## Notation

We provide an elaborator so that `R(G, H)` expands to `Ramsey G H` for 2 arguments,
or `graphRamseyNum ![G, H, ...]` for more arguments.
-/

@[expose] public section

namespace SimpleGraph

/--
An n-coloring of the edges of a graph `F` is a family of subgraphs `c : Fin n → SimpleGraph V`
such that they are pairwise edge-disjoint and their union equals `F`.
-/
def IsEdgeColoring {V : Type*} (F : SimpleGraph V) (n : ℕ) (c : Fin n → SimpleGraph V) : Prop :=
  (∀ i, c i ≤ F) ∧
  (∀ i j, i ≠ j → Disjoint (c i) (c j)) ∧
  (⨆ i, c i) = F

/--
The graph Ramsey number `R(H₀, H₁, ..., Hₙ₋₁)` is the smallest natural number `N` such that
for any edge-coloring of `K_N` into `n` colors, there exists a color `i` with `Hᵢ` contained
in the `i`-th color class.

This is the non-induced graph Ramsey number.
-/
noncomputable def graphRamseyNum {n : ℕ} {V : Fin n → Type*} [∀ i, Fintype (V i)]
    (H : (i : Fin n) → SimpleGraph (V i)) : ℕ :=
  sInf { N | ∀ (c : Fin n → SimpleGraph (Fin N)),
    IsEdgeColoring (⊤ : SimpleGraph (Fin N)) n c →
    ∃ i, (H i).IsContained (c i) }

/--
The 2-ary graph Ramsey number `R(G, H)` is the smallest natural number `N` such that
for any graph `R` on `N` vertices, either `G` is contained in `R` or `H` is contained in `Rᶜ`.

This is a direct definition equivalent to the 2-ary case of `graphRamseyNum`.
-/
noncomputable def Ramsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { N | ∀ (R : SimpleGraph (Fin N)), G.IsContained R ∨ H.IsContained Rᶜ }

/-- If the 2-color complement property holds at `N`, then `Ramsey G H ≤ N`. -/
lemma Ramsey.le {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} {N : ℕ}
    (h : ∀ R : SimpleGraph (Fin N), G.IsContained R ∨ H.IsContained Rᶜ) :
    Ramsey G H ≤ N :=
  Nat.sInf_le h

end SimpleGraph

/-!
## Notation

We define `R(G, H, ...)` as syntax for `graphRamseyNum ![G, H, ...]`.
-/

open Lean in
/-- Syntax for Ramsey numbers: `R(G, H)` or `R(G, H, K)` etc. -/
syntax (name := ramseyNotation) "R(" term,+ ")" : term

open Lean Elab Term in
/-- Elaborator for `R(G, H, ...)` that expands to `Ramsey G H` for 2 args
    or `graphRamseyNum ![G, H, ...]` for more args. -/
@[term_elab ramseyNotation]
meta def elabRamseyNotation : TermElab := fun stx _ => do
  match stx with
  | `(R($args,*)) =>
    let argsArr := args.getElems
    if argsArr.size == 2 then
      -- For exactly 2 arguments, use the direct Ramsey function (handles heterogeneous types)
      let g := argsArr[0]!
      let h := argsArr[1]!
      elabTerm (← `(SimpleGraph.Ramsey $g $h)) none
    else
      -- For n > 2 arguments, use graphRamseyNum with matrix notation
      let matrixLit ← `(![$[$argsArr],*])
      elabTerm (← `(SimpleGraph.graphRamseyNum $matrixLit)) none
  | _ => throwUnsupportedSyntax
