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
# Erdős Problem 719

*Reference:* [erdosproblems.com/719](https://www.erdosproblems.com/719)

A conjecture of Erdős and Sauer.

[Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*, 1981.
-/

open Finset

namespace Erdos719

/-- An $r$-uniform hypergraph on `Fin n`: a family of $r$-element subsets. -/
def IsRUniformHypergraph (n r : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = r

/-- An $r$-uniform hypergraph is $K_{r+1}^r$-free: no $(r+1)$-element vertex set has
all its $r$-element subsets as edges. -/
def IsHypergraphCliqueFree (r : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ¬∃ S : Finset (Fin n), S.card = r + 1 ∧ Finset.powersetCard r S ⊆ H

/-- The Turán number $\mathrm{ex}_r(n; K_{r+1}^r)$: the maximum number of edges in an
$r$-uniform $K_{r+1}^r$-free hypergraph on $n$ vertices. -/
noncomputable def turanHypergraphNumber (n r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ H : Finset (Finset (Fin n)),
    IsRUniformHypergraph n r H ∧ H.card = k ∧ IsHypergraphCliqueFree r H}

/-- The edges of a decomposition piece: if $S$ has $r$ elements (a $K_r^r$ copy),
it contributes the single edge $\{S\}$; if $S$ has $r+1$ elements (a $K_{r+1}^r$ copy),
it contributes all $r$-element subsets of $S$. -/
def pieceEdges (r : ℕ) {n : ℕ} (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  if S.card = r then {S}
  else if S.card = r + 1 then Finset.powersetCard r S
  else ∅

/--
Erdős Problem 719 (Erdős–Sauer conjecture) [Er81]:

Is every $r$-uniform hypergraph $G$ on $n$ vertices the union of at most
$\mathrm{ex}_r(n; K_{r+1}^r)$ edge-disjoint copies of $K_r^r$ (single edges) and $K_{r+1}^r$
(complete $(r+1)$-cliques)?
-/
@[category research open, AMS 5]
theorem erdos_719 : answer(sorry) ↔ ∀ (n r : ℕ) (H : Finset (Finset (Fin n))),
    IsRUniformHypergraph n r H →
    ∃ (pieces : Finset (Finset (Fin n))),
      (∀ S ∈ pieces, S.card = r ∨ S.card = r + 1) ∧
      (∀ e ∈ H, ∃ S ∈ pieces, e ∈ pieceEdges r S) ∧
      (∀ S ∈ pieces, ∀ e ∈ pieceEdges r S, e ∈ H) ∧
      (∀ S₁ ∈ pieces, ∀ S₂ ∈ pieces, S₁ ≠ S₂ →
        Disjoint (pieceEdges r S₁) (pieceEdges r S₂)) ∧
      pieces.card ≤ turanHypergraphNumber n r := by
  sorry

end Erdos719
