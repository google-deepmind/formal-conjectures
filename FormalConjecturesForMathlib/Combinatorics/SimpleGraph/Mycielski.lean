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
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs

/-!
# The Mycielski construction

The Mycielski construction preserves triangle-freeness and increases a finite chromatic
number by one. Iteration gives finite graphs of clique number two with every chromatic
number at least two.

## References

- J. Mycielski, *Sur le coloriage des graphs*, Colloquium Mathematicum 3 (1955), 161–162.
  [doi:10.4064/cm-3-2-161-162](https://doi.org/10.4064/cm-3-2-161-162)
- [Erdős problem 627](https://www.erdosproblems.com/627)
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- The adjacency relation of the Mycielski construction. The apex is `none`;
original vertices use `Sum.inl`, and shadow vertices use `Sum.inr`. -/
def mycielskiAdj (G : SimpleGraph V) : Option (V ⊕ V) → Option (V ⊕ V) → Prop
  | none, some (.inr _) => True
  | some (.inr _), none => True
  | some (.inl v), some (.inl w) => G.Adj v w
  | some (.inl v), some (.inr w) => G.Adj v w
  | some (.inr v), some (.inl w) => G.Adj v w
  | _, _ => False

/-- The Mycielski construction adds a shadow copy of the vertices and an apex. -/
def mycielski (G : SimpleGraph V) : SimpleGraph (Option (V ⊕ V)) where
  Adj := mycielskiAdj G
  symm := ⟨by
    rintro (_ | (_ | _)) (_ | (_ | _)) <;> simp [mycielskiAdj, G.adj_comm]⟩
  loopless := ⟨by
    rintro (_ | (_ | _)) <;> simp [mycielskiAdj]⟩

@[simp] theorem mycielski_adj (G : SimpleGraph V) (v w : Option (V ⊕ V)) :
    G.mycielski.Adj v w ↔ mycielskiAdj G v w := Iff.rfl


variable {G : SimpleGraph V} {α : Type*} {k : ℕ}

/-- Extend a coloring by giving the apex a new color and each shadow its
original vertex's color. -/
def Coloring.mycielski (C : G.Coloring α) : G.mycielski.Coloring (Option α) :=
  Coloring.mk
    (fun
      | none => none
      | some (.inl v) => some (C v)
      | some (.inr v) => some (C v))
    (by
      rintro (_ | (_ | v)) (_ | (_ | w)) h <;>
        simp_all [mycielskiAdj, C.valid])

/-- A `k`-coloring extends to a `(k + 1)`-coloring of the Mycielski graph. -/
theorem Colorable.mycielski (h : G.Colorable k) : G.mycielski.Colorable (k + 1) := by
  simpa using h.some.mycielski.colorable

/-- Recolor every original vertex with the apex color using its shadow's
color. This produces a coloring of the original graph that omits the apex color. -/
noncomputable def Coloring.ofMycielski (C : G.mycielski.Coloring α) : G.Coloring α := by
  classical
  refine Coloring.mk (fun v => if C (some (.inl v)) = C none
    then C (some (.inr v)) else C (some (.inl v))) ?_
  intro v w h
  have hoo : C (some (.inl v)) ≠ C (some (.inl w)) := C.valid h
  have hos : C (some (.inl v)) ≠ C (some (.inr w)) := C.valid h
  have hso : C (some (.inr v)) ≠ C (some (.inl w)) := C.valid h
  split_ifs with hv hw
  · exact False.elim (hoo (hv.trans hw.symm))
  · exact hso
  · exact hos
  · exact hoo

/-- The recolored original graph omits the apex color. -/
theorem Coloring.ofMycielski_ne_apex (C : G.mycielski.Coloring α) (v : V) :
    C.ofMycielski v ≠ C none := by
  classical
  change (if C (some (.inl v)) = C none then C (some (.inr v))
    else C (some (.inl v))) ≠ C none
  split_ifs with h
  · exact C.valid (show G.mycielski.Adj (some (.inr v)) none from trivial)
  · exact h

/-- A Mycielski graph is not `k`-colorable if the original graph has chromatic number at least `k`. -/
theorem not_colorable_mycielski (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    ¬G.mycielski.Colorable k := by
  rintro ⟨C⟩
  obtain ⟨v, hv⟩ := (le_chromaticNumber_iff_forall_surjective.mp h)
    C.ofMycielski (C none)
  exact C.ofMycielski_ne_apex v hv

/-- The Mycielski construction increases a finite chromatic number by one. -/
theorem chromaticNumber_mycielski (h : G.chromaticNumber = (k : ℕ∞)) :
    G.mycielski.chromaticNumber = ((k + 1 : ℕ) : ℕ∞) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨(chromaticNumber_le_iff_colorable.mp h.le).mycielski,
        not_colorable_mycielski h.ge⟩)

/-- The Mycielski construction preserves triangle-freeness. -/
theorem CliqueFree.mycielski {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    G.mycielski.CliqueFree 3 := by
  classical
  have htri (a b c : V) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
      False := hG {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;>
    rcases c with _ | (_ | _) <;> simp_all only [mycielski_adj, mycielskiAdj]
  all_goals exact htri _ _ _ hab hac hbc

/-- A triangle-free graph has clique number at most two. -/
theorem CliqueFree.cliqueNum_le_two {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    G.cliqueNum ≤ 2 := by
  by_contra h
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact (CliqueFree.mono (by omega : 3 ≤ G.cliqueNum) hG) s hs

/-- The Mycielski graph of a nonempty triangle-free finite graph has clique number two. -/
theorem cliqueNum_mycielski [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hG : G.CliqueFree 3) : G.mycielski.cliqueNum = 2 := by
  classical
  apply Nat.le_antisymm hG.mycielski.cliqueNum_le_two
  obtain ⟨v⟩ := ‹Nonempty V›
  have hpair : G.mycielski.IsClique
      ({none, some (Sum.inr v)} : Finset (Option (V ⊕ V))) := by
    simp [mycielskiAdj]
  simpa using hpair.card_le_cliqueNum

variable {W : Type*}

/-- Relabelling vertices preserves the clique number. -/
theorem cliqueNum_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e).cliqueNum = G.cliqueNum := by
  unfold cliqueNum
  congr 1
  ext n
  change ((G.map e).cliqueSet n).Nonempty ↔ (G.cliqueSet n).Nonempty
  rw [cliqueSet_map_of_equiv]
  exact Set.image_nonempty

/-- Relabelling vertices preserves the chromatic number. -/
theorem chromaticNumber_map_equiv (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e).chromaticNumber = G.chromaticNumber := by
  exact le_antisymm
    (chromaticNumber_mono_of_hom (Iso.map e G).symm.toHom)
    (chromaticNumber_mono_of_hom (Iso.map e G).toHom)

/-- For every `k ≥ 2`, a finite graph has clique number two and chromatic number `k`. -/
theorem exists_cliqueNum_eq_two_chromaticNumber_eq (k : ℕ) (hk : 2 ≤ k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞) := by
  classical
  have hex (j : ℕ) : ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ G.cliqueNum = 2 ∧ G.chromaticNumber = ((j + 2 : ℕ) : ℕ∞) := by
    induction j with
    | zero =>
      refine ⟨Fin 2, inferInstance, inferInstance, ⊤, ?_, ?_, by simp⟩
      · exact cliqueFree_of_chromaticNumber_lt (by simp; decide)
      · apply Nat.le_antisymm
        · exact (cliqueFree_of_chromaticNumber_lt (by simp; decide) :
            (⊤ : SimpleGraph (Fin 2)).CliqueFree 3).cliqueNum_le_two
        · have h : (⊤ : SimpleGraph (Fin 2)).IsClique (Finset.univ : Finset (Fin 2)) :=
            by simp
          simpa using h.card_le_cliqueNum
    | succ j ih =>
      obtain ⟨V, hV, hne, G, htri, _, hχ⟩ := ih
      let := hV
      let := hne
      refine ⟨Option (V ⊕ V), inferInstance, inferInstance, G.mycielski,
        htri.mycielski, cliqueNum_mycielski htri, ?_⟩
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 2] using
        chromaticNumber_mycielski hχ
  obtain ⟨V, hV, _, G, _, hω, hχ⟩ := hex (k - 2)
  let := hV
  refine ⟨Fintype.card V, G.map (Fintype.equivFin V), ?_, ?_⟩
  · simpa only [cliqueNum_map_equiv] using hω
  · simpa only [chromaticNumber_map_equiv, Nat.sub_add_cancel hk] using hχ

end SimpleGraph
