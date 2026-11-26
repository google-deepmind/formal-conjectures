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

public import FormalConjecturesUtil

/-!
# Finite results for Erdős Problem 500

*Reference:* [erdosproblems.com/500](https://www.erdosproblems.com/500)
-/

@[expose] public section

namespace Erdos500Finite

abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

abbrev Uniform3 {n : ℕ} (E : Hypergraph n) : Prop := E.IsUniform 3

def K4Free {n : ℕ} (E : Hypergraph n) : Prop :=
  ∀ s : Finset (Fin n), s.card = 4 → ∃ t ⊆ s, t.card = 3 ∧ t ∉ E

def Admissible {n : ℕ} (E : Hypergraph n) : Prop := Uniform3 E ∧ K4Free E

/-- The witness formulation is exactly the absence of a complete four-vertex
3-uniform subhypergraph. -/
@[category API, AMS 5]
theorem k4Free_iff_no_complete_four {n : ℕ} {E : Hypergraph n} :
    K4Free E ↔ ∀ s : Finset (Fin n), s.card = 4 → ¬ s.powersetCard 3 ⊆ E := by
  classical
  constructor
  · intro h s hs hsubset
    obtain ⟨t, hts, hcard, hnot⟩ := h s hs
    exact hnot (hsubset (Finset.mem_powersetCard.mpr ⟨hts, hcard⟩))
  · intro h s hs
    have hn := h s hs
    simp only [Finset.subset_iff, Finset.mem_powersetCard, not_forall] at hn
    obtain ⟨t, ht, hnot⟩ := hn
    exact ⟨t, ht.1, ht.2, hnot⟩

instance {n : ℕ} (E : Hypergraph n) : Decidable (Uniform3 E) :=
  inferInstanceAs (Decidable (∀ e ∈ E, e.card = 3))

instance {n : ℕ} (E : Hypergraph n) : Decidable (K4Free E) :=
  inferInstanceAs (Decidable (∀ s : Finset (Fin n), s.card = 4 →
    ∃ t ⊆ s, t.card = 3 ∧ t ∉ E))

instance {n : ℕ} (E : Hypergraph n) : Decidable (Admissible E) :=
  inferInstanceAs (Decidable (Uniform3 E ∧ K4Free E))

def triples (n : ℕ) : Hypergraph n := Finset.univ.powersetCard 3

def admissibleGraphs (n : ℕ) : Finset (Hypergraph n) :=
  (triples n).powerset.filter Admissible

/-- The finite maximum number of edges in a tetrahedron-free triple system. -/
def extremal (n : ℕ) : ℕ := (admissibleGraphs n).sup Finset.card

@[category API, AMS 5]
theorem uniform3_iff_subset_triples {n : ℕ} {E : Hypergraph n} :
    Uniform3 E ↔ E ⊆ triples n := by
  simp [Finset.IsUniform, triples, Finset.subset_iff]

/-- The missing-triple condition agrees with the repository's complete-hypergraph API. -/
@[category API, AMS 5]
theorem k4Free_iff_not_containsCompleteHypergraph {n : ℕ} (E : Hypergraph n) :
    K4Free E ↔ ¬ E.ContainsCompleteHypergraph 3 4 := by
  rw [k4Free_iff_no_complete_four]
  simp [Finset.ContainsCompleteHypergraph]

/-- The computable finite maximum agrees with the repository's extremal number. -/
@[category API, AMS 5]
theorem extremal_eq_cliqueExtremalNumber (n : ℕ) :
    extremal n = _root_.Hypergraph.cliqueExtremalNumber n 3 4 := by
  classical
  unfold extremal admissibleGraphs _root_.Hypergraph.cliqueExtremalNumber
    _root_.Hypergraph.extremalNumber
  congr 1
  ext E
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hE, h⟩
    exact ⟨hE, (k4Free_iff_not_containsCompleteHypergraph E).mp h.2⟩
  · rintro ⟨hE, h⟩
    exact ⟨hE, uniform3_iff_subset_triples.mpr (Finset.mem_powerset.mp hE),
      (k4Free_iff_not_containsCompleteHypergraph E).mpr h⟩

@[category API, AMS 5]
theorem mem_admissibleGraphs {n : ℕ} {E : Hypergraph n} :
    E ∈ admissibleGraphs n ↔ Admissible E := by
  simp only [admissibleGraphs, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨uniform3_iff_subset_triples.mp h.1, h⟩⟩

@[category API, AMS 5]
theorem empty_admissible (n : ℕ) : Admissible (∅ : Hypergraph n) := by
  constructor
  · simp
  · intro s hs
    obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq (s := s) (n := 3) (by omega)
    exact ⟨t, ht, hcard, by simp⟩

@[category API, AMS 5]
theorem admissibleGraphs_nonempty (n : ℕ) : (admissibleGraphs n).Nonempty :=
  ⟨∅, mem_admissibleGraphs.mpr (empty_admissible n)⟩

@[category API, AMS 5]
theorem card_le_extremal {n : ℕ} {E : Hypergraph n} (hE : Admissible E) :
    E.card ≤ extremal n :=
  Finset.le_sup (mem_admissibleGraphs.mpr hE)

@[category API, AMS 5]
theorem extremal_attained (n : ℕ) :
    ∃ E : Hypergraph n, Admissible E ∧ E.card = extremal n := by
  obtain ⟨E, hE, heq⟩ := Finset.sup_mem_of_nonempty
    (f := Finset.card) (admissibleGraphs_nonempty n)
  exact ⟨E, mem_admissibleGraphs.mp hE, heq⟩

@[category API, AMS 5]
theorem extremal_le_iff (n k : ℕ) :
    extremal n ≤ k ↔ ∀ E : Hypergraph n, Admissible E → E.card ≤ k := by
  simp only [extremal, Finset.sup_le_iff, mem_admissibleGraphs]

@[category API, AMS 5]
theorem extremal_le_choose (n : ℕ) : extremal n ≤ n.choose 3 := by
  apply (extremal_le_iff n _).mpr
  intro E hE
  have h := Finset.card_le_card (uniform3_iff_subset_triples.mp hE.1)
  simpa [triples, Finset.card_powersetCard] using h

@[category API, AMS 5]
theorem extremal_eq_zero_of_lt_three {n : ℕ} (hn : n < 3) : extremal n = 0 := by
  have h := extremal_le_choose n
  rw [Nat.choose_eq_zero_of_lt hn] at h
  omega

@[category test, AMS 5]
theorem extremal_zero : extremal 0 = 0 := extremal_eq_zero_of_lt_three (by omega)
@[category test, AMS 5]
theorem extremal_one : extremal 1 = 0 := extremal_eq_zero_of_lt_three (by omega)
@[category test, AMS 5]
theorem extremal_two : extremal 2 = 0 := extremal_eq_zero_of_lt_three (by omega)

@[category test, AMS 5]
theorem extremal_three : extremal 3 = 1 := by
  have hl : 1 ≤ extremal 3 := by
    have h := card_le_extremal (E := triples 3) (by decide : Admissible (triples 3))
    simpa [triples, Finset.card_powersetCard] using h
  have hu := extremal_le_choose 3
  norm_num at hu
  omega

/-- A three-edge hypergraph on four vertices, obtained by deleting one triple. -/
def threeEdgesOnFour : Hypergraph 4 := (triples 4).erase {0, 1, 2}

@[category test, AMS 5]
theorem threeEdgesOnFour_admissible : Admissible threeEdgesOnFour := by decide

@[category test, AMS 5]
theorem threeEdgesOnFour_card : threeEdgesOnFour.card = 3 := by decide

@[category test, AMS 5]
theorem extremal_four : extremal 4 = 3 := by
  have hl : 3 ≤ extremal 4 := by
    simpa only [threeEdgesOnFour_card] using card_le_extremal threeEdgesOnFour_admissible
  obtain ⟨E, hE, heq⟩ := extremal_attained 4
  have hbound := extremal_le_choose 4
  norm_num at hbound
  have hlt : E.card < 4 := by
    by_contra hnot
    have hcard : (triples 4).card ≤ E.card := by
      simp only [triples, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      norm_num
      omega
    have hfull := Finset.eq_of_subset_of_card_le
      (uniform3_iff_subset_triples.mp hE.1) hcard
    have hn : ¬ K4Free (triples 4) := by decide
    exact hn (hfull ▸ hE.2)
  omega

/-- Three colours, with the cyclic orientation `a ↦ a + 1`. -/
def turanPattern (a b c : Fin 3) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨
  (a = b ∧ c = a + 1) ∨
  (a = c ∧ b = a + 1) ∨
  (b = c ∧ a = b + 1)

instance (a b c : Fin 3) : Decidable (turanPattern a b c) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)))

/-- The elementary, finite obstruction underlying Turán's cyclic construction. -/
@[category API, AMS 5]
theorem four_colour_obstruction (a b c d : Fin 3) :
    ¬ (turanPattern a b c ∧ turanPattern a b d ∧
      turanPattern a c d ∧ turanPattern b c d) := by
  revert a b c d
  decide

/-- An arbitrary three-colouring gives the cyclic Turán triple system. -/
def turanConstruction {n : ℕ} (colour : Fin n → Fin 3) : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.powersetCard 3).filter fun e =>
    ∀ x ∈ e, ∀ y ∈ e, ∀ z ∈ e, x ≠ y → x ≠ z → y ≠ z →
      turanPattern (colour x) (colour y) (colour z)

@[category API, AMS 5]
theorem mem_turanConstruction {n : ℕ} {colour : Fin n → Fin 3}
    {e : Finset (Fin n)} : e ∈ turanConstruction colour ↔
    e.card = 3 ∧
    ∀ x ∈ e, ∀ y ∈ e, ∀ z ∈ e, x ≠ y → x ≠ z → y ≠ z →
      turanPattern (colour x) (colour y) (colour z) := by
  classical
  simp [turanConstruction]

@[category API, AMS 5]
theorem turanConstruction_uniform {n : ℕ} (colour : Fin n → Fin 3) :
    ∀ e ∈ turanConstruction colour, e.card = 3 := by
  intro e he
  exact (mem_turanConstruction.mp he).1

/-- No four vertices span all four triples in the cyclic construction. -/
@[category API, AMS 5]
theorem turanConstruction_K4Free {n : ℕ} (colour : Fin n → Fin 3) :
    ∀ s : Finset (Fin n), s.card = 4 →
      ∃ t ⊆ s, t.card = 3 ∧ t ∉ turanConstruction colour := by
  classical
  intro s hs
  by_contra h
  push Not at h
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.mp hs
  have get (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hx : x ∈ ({a, b, c, d} : Finset (Fin n)))
      (hy : y ∈ ({a, b, c, d} : Finset (Fin n)))
      (hz : z ∈ ({a, b, c, d} : Finset (Fin n))) :
      turanPattern (colour x) (colour y) (colour z) := by
    have ht : ({x, y, z} : Finset (Fin n)) ∈ turanConstruction colour := by
      apply h
      · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
          And.intro hx (And.intro hy hz)
      · simp [hxy, hxz, hyz]
    exact (mem_turanConstruction.mp ht).2 x (by simp) y (by simp) z (by simp)
      hxy hxz hyz
  exact four_colour_obstruction (colour a) (colour b) (colour c) (colour d)
    ⟨get a b c hab hac hbc (by simp) (by simp) (by simp),
      get a b d hab had hbd (by simp) (by simp) (by simp),
      get a c d hac had hcd (by simp) (by simp) (by simp),
      get b c d hbc hbd hcd (by simp) (by simp) (by simp)⟩

def balancedSixColour (v : Fin 6) : Fin 3 := ⟨v.val % 3, Nat.mod_lt _ (by omega)⟩

@[category test, AMS 5]
theorem balancedSixConstruction_card : (turanConstruction balancedSixColour).card = 14 := by
  decide

/-- Turán's balanced six-vertex construction shows that $\mathrm{ex}_3(6,K_4^3)\geq14$. -/
@[category textbook, AMS 5]
theorem fourteen_le_extremal_six : 14 ≤ extremal 6 := by
  have h := card_le_extremal (E := turanConstruction balancedSixColour)
    ⟨turanConstruction_uniform _, turanConstruction_K4Free _⟩
  simpa only [balancedSixConstruction_card] using h

/-- Turán's balanced six-vertex construction gives $\mathrm{ex}_3(6,K_4^3)\geq14$. -/
@[category textbook, AMS 5]
theorem erdos_500.variants.six_vertices :
    14 ≤ _root_.Hypergraph.cliqueExtremalNumber 6 3 4 := by
  rw [← extremal_eq_cliqueExtremalNumber]
  exact fourteen_le_extremal_six
end Erdos500Finite
