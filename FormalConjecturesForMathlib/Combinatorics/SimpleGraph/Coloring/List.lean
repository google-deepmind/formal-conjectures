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

/-- A graph is $(a,b)$-choosable if for any assignment of a list of $a$ colours to each of its
vertices there is a subset of $b$ colours from each list such that the subsets of adjacent
vertices are disjoint. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = a) →
    ∃ φ : V → Finset ℕ, (∀ v, φ v ⊆ L v ∧ (φ v).card = b) ∧
      ∀ u v, G.Adj u v → Disjoint (φ u) (φ v)

/-- Ordinary list colorability is exactly `(a,1)`-choosability. -/
theorem isChoosable_one_iff {V : Type*} (G : SimpleGraph V) (a : ℕ) :
    G.IsChoosable a 1 ↔ G.IsKChoosable a := by
  classical
  constructor
  · intro h L hL
    obtain ⟨φ, hφ, hdis⟩ := h L hL
    choose c hc using fun v ↦ Finset.card_eq_one.mp (hφ v).2
    have hmem (v : V) : c v ∈ φ v := by rw [hc v]; simp
    refine ⟨Coloring.mk c ?_, fun v ↦ (hφ v).1 (hmem v)⟩
    intro u v huv heq
    exact Finset.disjoint_left.mp (hdis u v huv) (hmem u) (heq ▸ hmem v)
  · intro h L hL
    obtain ⟨c, hc⟩ := h L hL
    refine ⟨fun v ↦ {c v}, ?_, ?_⟩
    · intro v
      simp [hc v]
    · intro u v huv
      simpa using c.valid huv

end SimpleGraph
