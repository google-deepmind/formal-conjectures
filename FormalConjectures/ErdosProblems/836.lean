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
# Erdős Problem 836

*Reference:* [erdosproblems.com/836](https://www.erdosproblems.com/836)

Let $r \geq 2$ and $G$ be an $r$-uniform hypergraph with chromatic number 3
(that is, there is a 3-colouring of the vertices of $G$ such that no edge
is monochromatic). Suppose any two edges of $G$ have a non-empty intersection.

Must $G$ contain $O(r^2)$ many vertices?
Must there be two edges which meet in $\gg r$ many vertices?

A problem of Erdős and Shelah [Er74d].

Alon showed the first question is false: there exists an intersecting
$r$-uniform 3-chromatic hypergraph with $\sim 4^r / \sqrt{r}$ vertices.

Erdős and Lovász [ErLo75] proved that there must be two edges meeting
in $\Omega(r / \log r)$ vertices. The second question ($\Omega(r)$) remains open.
-/

open Finset

namespace Erdos836

/-- A hypergraph on vertex type $V$. -/
structure Hypergraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)

/-- A hypergraph is $r$-uniform if every edge has exactly $r$ vertices. -/
def Hypergraph.IsUniform {V : Type*} [DecidableEq V] (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- The vertices of a hypergraph (the union of all edges). -/
def Hypergraph.vertices {V : Type*} [DecidableEq V] (H : Hypergraph V) : Finset V :=
  H.edges.biUnion id

/-- A proper coloring of a hypergraph: no edge is monochromatic. -/
def Hypergraph.IsProperColoring {V : Type*} [DecidableEq V] (H : Hypergraph V)
    {α : Type*} (f : V → α) : Prop :=
  ∀ e ∈ H.edges, e.card ≥ 2 → ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- A hypergraph has chromatic number 3: it is 3-colorable but not 2-colorable. -/
def Hypergraph.HasChromaticNumber3 {V : Type*} [DecidableEq V] (H : Hypergraph V) : Prop :=
  (∃ f : V → Fin 3, H.IsProperColoring f) ∧
  (∀ f : V → Fin 2, ¬H.IsProperColoring f)

/-- A hypergraph is intersecting if any two edges share at least one vertex. -/
def Hypergraph.IsIntersecting {V : Type*} [DecidableEq V] (H : Hypergraph V) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, (e₁ ∩ e₂).Nonempty

/--
Erdős Problem 836 [Er74d]:

For every $r$-uniform intersecting hypergraph with chromatic number 3,
there exist two edges meeting in $\Omega(r)$ vertices.

Formally: there exists a constant $C > 0$ such that for all $r \geq 2$ and for every
such hypergraph, there exist two distinct edges whose intersection has
size $\geq C \cdot r$.

Erdős and Lovász [ErLo75] proved the weaker bound $\Omega(r / \log r)$.
-/
@[category research open, AMS 5]
theorem erdos_836 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧
    ∀ r : ℕ, r ≥ 2 →
    ∀ (n : ℕ) (H : Hypergraph (Fin n)),
      H.IsUniform r →
      H.HasChromaticNumber3 →
      H.IsIntersecting →
      ∃ e₁ ∈ H.edges, ∃ e₂ ∈ H.edges, e₁ ≠ e₂ ∧
        ((e₁ ∩ e₂).card : ℝ) ≥ C * (r : ℝ) := by
  sorry

end Erdos836
