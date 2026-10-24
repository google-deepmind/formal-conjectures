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

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace SimpleGraph

/-- The vertices of `G` can be covered by at most `k` paths. Paths may overlap, and a
single vertex counts as a path. -/
def HasPathCover {α : Type*} (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (P : Fin m → (u : α) × (v : α) × G.Walk u v), m ≤ k ∧
    (∀ i, (P i).2.2.IsPath) ∧ ∀ x : α, ∃ i, x ∈ (P i).2.2.support

lemma HasPathCover.mono {α : Type*} {G : SimpleGraph α} {k l : ℕ}
    (h : G.HasPathCover k) (hkl : k ≤ l) : G.HasPathCover l := by
  obtain ⟨m, P, hm, hp, hc⟩ := h
  exact ⟨m, P, hm.trans hkl, hp, hc⟩

@[simp] lemma hasPathCover_zero_iff {α : Type*} (G : SimpleGraph α) :
    G.HasPathCover 0 ↔ IsEmpty α := by
  constructor
  · rintro ⟨m, P, hm, hp, hc⟩
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    exact ⟨fun x => by obtain ⟨i, hi⟩ := hc x; exact Fin.elim0 i⟩
  · intro h
    exact ⟨0, Fin.elim0, le_rfl, fun i => Fin.elim0 i, fun x => False.elim (h.false x)⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

end SimpleGraph
