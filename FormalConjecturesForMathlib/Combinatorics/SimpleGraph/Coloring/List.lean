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

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# List colourings

`IsKChoosable G k` says that `G` is $k$-choosable, and `listChromaticNumber G` is the list
chromatic number (choice number) $\chi_L(G)$ of Erdős, Rubin and Taylor.

## References

* P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*. Proceedings of the West Coast
  Conference on Combinatorics, Graph Theory and Computing (1979), Congress. Numer. XXVI (1980),
  125-157.
-/

namespace SimpleGraph

/--
A graph $G$ is $k$-choosable if for any assignment of a list of $k$ colours to each vertex of $G$
(perhaps different lists for different vertices) a colouring of each vertex by a colour on its list
can be chosen such that adjacent vertices receive distinct colours.
-/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/--
The list chromatic number $\chi_L(G)$, defined to be the minimal $k$ such that $G$ is
$k$-choosable. It is `0` if $G$ is not $k$-choosable for any $k$, which can only happen for an
infinite graph.
-/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/-- A $k$-choosable graph is $k$-colourable: give every vertex the list $\{0, \ldots, k-1\}$. -/
theorem IsKChoosable.colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (h : G.IsKChoosable k) :
    G.Colorable k := by
  obtain ⟨C, hC⟩ := h (fun _ => Finset.range k) (fun _ => Finset.card_range k)
  exact ⟨Coloring.mk (fun v => ⟨C v, Finset.mem_range.1 (hC v)⟩)
    fun hab heq => C.valid hab (congrArg Fin.val heq)⟩

end SimpleGraph
