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
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Lean.Elab.Tactic.Omega

/-!
# Acyclic vertex colorings

A proper coloring is acyclic if no cycle uses at most two colors.
The acyclic chromatic number takes values in the extended natural numbers.
-/

@[expose] public section

namespace SimpleGraph

variable {V C D : Type*} {G : SimpleGraph V}

/-- A proper coloring with no cycle using at most two colors. -/
def Coloring.IsAcyclic (c : G.Coloring C) : Prop :=
  ∀ (v : V) (w : G.Walk v v), w.IsCycle →
    ¬ ∃ a b : C, ∀ u ∈ w.support, c u = a ∨ c u = b

/-- Existence of an acyclic coloring with `k` available colors. -/
def AcyclicColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : G.Coloring (Fin k), c.IsAcyclic

/-- Least finite acyclic palette size, or infinity if no finite palette suffices. -/
noncomputable def acyclicChromaticNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ k ∈ Set.ofPred G.AcyclicColorable, (k : ℕ∞)

theorem acyclicColorable_iff_exists (k : ℕ) :
    G.AcyclicColorable k ↔ ∃ c : V → Fin k,
      (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) ∧
      ∀ (v : V) (w : G.Walk v v), w.IsCycle →
        ¬ ∃ a b : Fin k, ∀ u ∈ w.support, c u = a ∨ c u = b := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun {_ _} h => c.valid h, hc⟩
  · rintro ⟨c, hp, hc⟩
    exact ⟨Coloring.mk c (fun {_ _} h => hp h), hc⟩

theorem Coloring.IsAcyclic.recolorOfEmbedding {c : G.Coloring C}
    (hc : c.IsAcyclic) (e : C ↪ D) :
    (G.recolorOfEmbedding e c).IsAcyclic := by
  classical
  intro v w hw
  rintro ⟨a, b, hab⟩
  let : Nonempty C := ⟨c v⟩
  apply hc v w hw
  refine ⟨Function.invFun e a, Function.invFun e b, ?_⟩
  intro u hu
  have h := hab u hu
  change e (c u) = a ∨ e (c u) = b at h
  rcases h with h | h
  · left
    simpa only [Function.leftInverse_invFun e.injective (c u)] using
      congrArg (Function.invFun e) h
  · right
    simpa only [Function.leftInverse_invFun e.injective (c u)] using
      congrArg (Function.invFun e) h

theorem AcyclicColorable.mono {k l : ℕ} (h : G.AcyclicColorable k) (hkl : k ≤ l) :
    G.AcyclicColorable l := by
  obtain ⟨c, hc⟩ := h
  let e : Fin k ↪ Fin l := ⟨Fin.castLE hkl, Fin.castLE_injective hkl⟩
  exact ⟨G.recolorOfEmbedding e c, hc.recolorOfEmbedding e⟩

theorem AcyclicColorable.colorable {k : ℕ} (h : G.AcyclicColorable k) :
    G.Colorable k := ⟨h.choose⟩

theorem AcyclicColorable.acyclicChromaticNumber_le {k : ℕ} (h : G.AcyclicColorable k) :
    G.acyclicChromaticNumber ≤ k :=
  iInf₂_le k h

theorem acyclicChromaticNumber_ne_top_iff_exists :
    G.acyclicChromaticNumber ≠ ⊤ ↔ ∃ k, G.AcyclicColorable k := by
  simp [acyclicChromaticNumber]

theorem AcyclicColorable.acyclicChromaticNumber_eq_sInf {k : ℕ}
    (h : G.AcyclicColorable k) :
    G.acyclicChromaticNumber = (sInf {n : ℕ | G.AcyclicColorable n} : ℕ) := by
  exact (ENat.natCast_sInf ⟨k, h⟩).symm

theorem acyclicChromaticNumber_le_iff_acyclicColorable {k : ℕ} :
    G.acyclicChromaticNumber ≤ k ↔ G.AcyclicColorable k := by
  refine ⟨fun h => ?_, AcyclicColorable.acyclicChromaticNumber_le⟩
  have hfinite : G.acyclicChromaticNumber ≠ ⊤ :=
    (h.trans_lt (ENat.natCast_lt_top k)).ne
  obtain ⟨m, hm⟩ := acyclicChromaticNumber_ne_top_iff_exists.mp hfinite
  rw [hm.acyclicChromaticNumber_eq_sInf, Nat.cast_le] at h
  exact (Nat.sInf_mem (show {n : ℕ | G.AcyclicColorable n}.Nonempty from ⟨m, hm⟩)).mono h

theorem chromaticNumber_le_acyclicChromaticNumber :
    G.chromaticNumber ≤ G.acyclicChromaticNumber := by
  unfold acyclicChromaticNumber
  exact le_iInf₂ fun k hk => hk.colorable.chromaticNumber_le

theorem Coloring.isAcyclic_of_injective (c : G.Coloring C)
    (hinj : Function.Injective c) : c.IsAcyclic := by
  classical
  intro v w hw
  rintro ⟨a, b, hab⟩
  have hn : (w.support.tail.map c).Nodup := hw.support_nodup.map hinj
  have hs : (w.support.tail.map c).toFinset ⊆ ({a, b} : Finset C) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    simpa using hab u (List.mem_of_mem_tail hu)
  have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le a {b})
  rw [List.toFinset_card_of_nodup hn, List.length_map, List.length_tail,
    w.length_support] at hc
  simp only [Finset.card_singleton] at hc
  have := hw.three_le_length
  omega

theorem acyclicColorable_of_fintype (G : SimpleGraph V) [Fintype V] :
    G.AcyclicColorable (Fintype.card V) := by
  let e := Fintype.equivFin V
  let c : G.Coloring (Fin (Fintype.card V)) :=
    Coloring.mk e (fun h => fun he => h.ne (e.injective he))
  exact ⟨c, c.isAcyclic_of_injective e.injective⟩

theorem acyclicChromaticNumber_ne_top (G : SimpleGraph V) [Finite V] :
    G.acyclicChromaticNumber ≠ ⊤ := by
  cases nonempty_fintype V
  exact acyclicChromaticNumber_ne_top_iff_exists.mpr
    ⟨_, G.acyclicColorable_of_fintype⟩

end SimpleGraph
