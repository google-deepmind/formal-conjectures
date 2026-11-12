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

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum

/-!
# Graph minors and planar simple graphs

Combinatorial graph minors via connected pairwise-disjoint branch sets and planarity of finite
simple graphs via Wagner's forbidden-minor theorem (excluding $K_5$ and $K_{3,3}$ minors).
-/

@[expose] public section

namespace SimpleGraph

variable {U V : Type*}

/-- `H.IsMinor G` means `H` occurs as a **graph minor** of `G`: its vertices map to pairwise
disjoint nonempty connected vertex subsets (`branch sets`) of `G` such that every edge of `H` is
realized by at least one edge of `G` between the corresponding branch sets. -/
def IsMinor (H : SimpleGraph U) (G : SimpleGraph V) : Prop :=
  ∃ B : U → Set V,
    (∀ u, (B u).Nonempty ∧ (G.induce (B u)).Preconnected) ∧
    Pairwise (fun u₁ u₂ => Disjoint (B u₁) (B u₂)) ∧
    ∀ ⦃u₁ u₂⦄, H.Adj u₁ u₂ → ∃ v₁ ∈ B u₁, ∃ v₂ ∈ B u₂, G.Adj v₁ v₂

/-- A finite simple graph `G` is **planar** (by Wagner's theorem) if neither $K_5$ nor $K_{3,3}$
is a minor of `G`. -/
def IsPlanar [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ (completeGraph (Fin 5)).IsMinor G ∧
    ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).IsMinor G

/-- Every simple graph is a minor of itself via singleton branch sets. -/
@[refl]
theorem IsMinor.refl (G : SimpleGraph V) : G.IsMinor G := by
  refine ⟨fun v => {v}, fun v => ⟨⟨v, rfl⟩, ?_⟩, fun u v huv => Set.disjoint_singleton.mpr huv,
    fun u v huv => ⟨u, rfl, v, rfl, huv⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Set.mem_singleton_iff] at ha hb
  subst ha hb
  exact Reachable.refl _

/-- Adding edges to the host graph preserves minors. -/
theorem IsMinor.mono_right {H : SimpleGraph U} {G G' : SimpleGraph V}
    (h : H.IsMinor G) (hGG' : G ≤ G') : H.IsMinor G' := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := h
  refine ⟨B, fun u => ⟨(hconn u).1, ?_⟩, hdisj, ?_⟩
  · intro x y
    exact ((hconn u).2 x y).mono fun _ _ huv => hGG' huv
  · intro u₁ u₂ hu
    obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := hadj hu
    exact ⟨v₁, hv₁, v₂, hv₂, hGG' hv⟩

/-- Removing edges from the pattern graph preserves minors. -/
theorem IsMinor.mono_left {H H' : SimpleGraph U} {G : SimpleGraph V}
    (hHH' : H ≤ H') (h : H'.IsMinor G) : H.IsMinor G := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := h
  exact ⟨B, hconn, hdisj, fun _ _ hu => hadj (hHH' hu)⟩

/-- If `H` is a minor of `G` on finite vertex types, then `|U| ≤ |V|`. -/
theorem IsMinor.card_le [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (h : H.IsMinor G) : Fintype.card U ≤ Fintype.card V := by
  obtain ⟨B, hconn, hdisj, -⟩ := h
  classical
  let pick : U → V := fun u => (hconn u).1.some
  have hinj : Function.Injective pick := fun u₁ u₂ heq => by
    by_contra hne
    have hmem : pick u₁ ∈ B u₂ := by
      rw [heq]
      exact (hconn u₂).1.some_mem
    exact Set.disjoint_left.mp (hdisj hne) (hconn u₁).1.some_mem hmem
  exact Fintype.card_le_of_injective pick hinj

/-- Any spanning subgraph of a finite planar graph is planar. -/
theorem IsPlanar.anti [Fintype V] {G G' : SimpleGraph V} (hG' : G'.IsPlanar) (h : G ≤ G') :
    G.IsPlanar :=
  ⟨fun h5 => hG'.1 (h5.mono_right h), fun h33 => hG'.2 (h33.mono_right h)⟩

/-- Every finite simple graph on at most $4$ vertices is planar. -/
theorem isPlanar_of_card_le_four [Fintype V] (G : SimpleGraph V) (hV : Fintype.card V ≤ 4) :
    G.IsPlanar := by
  refine ⟨fun h5 => ?_, fun h33 => ?_⟩
  · have hle := h5.card_le
    simp only [Fintype.card_fin] at hle
    omega
  · have hle := h33.card_le
    simp only [Fintype.card_sum, Fintype.card_fin] at hle
    omega

/-- The edgeless graph on any finite vertex type is planar. -/
@[simp]
theorem isPlanar_bot [Fintype V] : (⊥ : SimpleGraph V).IsPlanar := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, _, hadj⟩
    obtain ⟨_, _, _, _, huv⟩ := hadj (show (completeGraph (Fin 5)).Adj 0 1 by decide)
    exact huv
  · rintro ⟨_, _, _, hadj⟩
    have h0 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (.inl 0) (.inr 0) := .inl ⟨rfl, rfl⟩
    obtain ⟨_, _, _, _, huv⟩ := hadj h0
    exact huv

/-- The complete graph $K_5$ is not planar. -/
@[simp]
theorem not_isPlanar_completeGraph_five : ¬ (completeGraph (Fin 5)).IsPlanar :=
  fun h => h.1 (.refl _)

/-- The complete bipartite graph $K_{3,3}$ is not planar. -/
@[simp]
theorem not_isPlanar_completeBipartiteGraph_three :
    ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).IsPlanar :=
  fun h => h.2 (.refl _)

end SimpleGraph
