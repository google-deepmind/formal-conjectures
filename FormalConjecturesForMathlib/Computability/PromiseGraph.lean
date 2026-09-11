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

public import FormalConjecturesForMathlib.Computability.MatrixGraphProblems
public import FormalConjecturesForMathlib.Computability.PromiseProblems
public import Mathlib.Data.Fintype.Pi

/-!
# Promise graph homomorphism

Inputs are explicit square Boolean adjacency matrices. They may be directed and
may contain loops, as in the promise digraph homomorphism problem in
Brakensiek–Guruswami, *Promise Constraint Satisfaction: Algebraic Structure and
a Symmetric Boolean Dichotomy*, §1, Conjecture 1.2:
https://arxiv.org/abs/1704.01937.
The conjecture fixes two undirected, loopless, non-bipartite target graphs.

Homomorphisms preserve every encoded edge, including loops. No symmetrization or
loop removal is performed on inputs. Exhaustive finite quantification supplies
decidable reference semantics, not a polynomial-time algorithm.
-/

@[expose] public section

namespace Computability.PromiseGraph

open MatrixGraph

/-- Existence of an edge-preserving map between the represented vertex sets. -/
def Hom (g h : Code) : Prop :=
  ∃ f : Fin g.length → Fin h.length,
    ∀ i j, entry g i j = true → entry h (f i) (f j) = true

instance (g h : Code) : Decidable (Hom g h) := by
  unfold Hom
  infer_instance

theorem Hom.refl (g : Code) : Hom g g := ⟨id, fun _ _ he => he⟩

theorem Hom.trans {g h k : Code} (hgh : Hom g h) (hhk : Hom h k) : Hom g k := by
  obtain ⟨f, hf⟩ := hgh
  obtain ⟨f', hf'⟩ := hhk
  exact ⟨f' ∘ f, fun i j he => hf' _ _ (hf i j he)⟩

/-- The represented graph has no proper coloring with two colors. -/
def Nonbipartite (g : Code) : Prop :=
  ¬ ∃ color : Fin g.length → Fin 2,
    ∀ i j, entry g i j = true → color i ≠ color j

instance (g : Code) : Decidable (Nonbipartite g) := by
  unfold Nonbipartite
  infer_instance

/-- A homomorphic image of a nonbipartite graph cannot be two-colored. -/
theorem Hom.nonbipartite {g h : Code} (hgh : Hom g h) (hg : Nonbipartite g) :
    Nonbipartite h := by
  rintro ⟨color, hc⟩
  obtain ⟨f, hf⟩ := hgh
  exact hg ⟨color ∘ f, fun i j he => hc _ _ (hf i j he)⟩

theorem nonbipartite_iff {g : Code} (hg : ValidGraph g) :
    Nonbipartite g ↔ ¬ (toGraph g).Colorable 2 := by
  unfold Nonbipartite
  apply not_congr
  constructor
  · rintro ⟨color, hc⟩
    exact ⟨SimpleGraph.Coloring.mk color
      (fun {i j} he => hc i j ((toGraph_adj hg i j).mp he))⟩
  · rintro ⟨color⟩
    exact ⟨color, fun i j he => color.valid ((toGraph_adj hg i j).mpr he)⟩

/-- The input maps to the strict target. -/
def Yes (g x : Code) : Prop := Square x ∧ Hom x g

/-- The input does not map to the relaxed target. -/
def No (h x : Code) : Prop := Square x ∧ ¬ Hom x h

instance (g x : Code) : Decidable (Yes g x) := by
  unfold Yes Square
  infer_instance

instance (h x : Code) : Decidable (No h x) := by
  unfold No Square
  infer_instance

theorem yes_not_no {g h x : Code} (hgh : Hom g h) (hy : Yes g x) : ¬ No h x := by
  intro hn
  exact hn.2 (hy.2.trans hgh)

/-- A loop in the input cannot be silently discarded when the target is loopless. -/
theorem not_hom_of_loop {g h : Code} (hh : ValidDigraph h)
    (i : Fin g.length) (hi : entry g i i = true) : ¬ Hom g h := by
  rintro ⟨f, hf⟩
  have he := hf i i hi
  rw [hh.2 (f i)] at he
  cases he

end Computability.PromiseGraph
