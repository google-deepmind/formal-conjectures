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
# Erdős Problem 117

*References:*
- [erdosproblems.com/117](https://www.erdosproblems.com/117)
- [Ne76] B. H. Neumann, *A problem of Paul Erdős on groups*. J. Austral. Math. Soc. Ser. A 21
  (1976), 467-472.
- [Py87] L. Pyber, *The number of pairwise non-commuting elements and the index of the centre in a
  finite group*. J. London Math. Soc. (2) 35 (1987), 287-295.
- [Le26] G. Lecomte, *Abelian covers and the index of the centre in a group*.
  [arXiv:2611.15068](https://arxiv.org/abs/2611.15068) (2026).
-/

@[expose] public section

namespace Erdos117

/-- Every finite subset of `G` with cardinality strictly greater than `n` contains two distinct
commuting elements. Equivalently, the clique number of the noncommuting graph of `G` is at most
`n`. -/
def HasNoPairwiseNoncommutingGt (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ s : Finset G, n < s.card → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ Commute x y

/-- A finite subset `S` of `G` is pairwise noncommuting if no two distinct elements commute. -/
def IsPairwiseNoncommuting {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y

/-- A subgroup `H` of `G` is abelian if all of its elements pairwise commute. -/
def IsAbelianSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, Commute x y

/-- A finite family `C` of subgroups is an abelian cover of `G` if every member of `C` is
abelian and every element of `G` belongs to at least one subgroup in `C`. -/
def IsAbelianCover (G : Type*) [Group G] (C : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ C, IsAbelianSubgroup H) ∧ ∀ g : G, ∃ H ∈ C, g ∈ H

/-- `G` can be covered by at most `m` abelian subgroups. -/
def HasAbelianCoverOfCardLe (G : Type*) [Group G] (m : ℕ) : Prop :=
  ∃ C : Finset (Subgroup G), IsAbelianCover G C ∧ C.card ≤ m

/-- `erdos117H n` is the minimal `m : ℕ` such that every group `G` in which every subset of size
strictly greater than `n` contains two distinct commuting elements can be covered by at most `m`
abelian subgroups. -/
noncomputable def erdos117H (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (G : Type) [Group G], HasNoPairwiseNoncommutingGt G n →
    HasAbelianCoverOfCardLe G m}

/-- Every abelian cover of a group is nonempty (`1 ≤ C.card`), since the identity `1 : G` must be
covered. -/
@[category API, AMS 20]
theorem one_le_card_of_isAbelianCover {G : Type*} [Group G] {C : Finset (Subgroup G)}
    (hC : IsAbelianCover G C) : 1 ≤ C.card := by
  rcases hC.2 (1 : G) with ⟨H, hHC, _⟩
  exact Finset.one_le_card.mpr ⟨H, hHC⟩

/-- An abelian group can be covered by a single abelian subgroup (`⊤`). -/
@[category API, AMS 20]
theorem hasAbelianCover_one_of_commute {G : Type*} [Group G]
    (hcomm : ∀ x y : G, Commute x y) : HasAbelianCoverOfCardLe G 1 := by
  refine ⟨{⊤}, ⟨?_, ?_⟩, by simp⟩
  · intro H _ x _ y _
    exact hcomm x y
  · intro g
    exact ⟨⊤, by simp, trivial⟩

/-- If every subset of `G` of size greater than `1` contains a commuting pair, then `G` is
abelian. -/
@[category API, AMS 20]
theorem commute_all_of_no_noncommuting_gt_one {G : Type*} [Group G]
    (h1 : HasNoPairwiseNoncommutingGt G 1) : ∀ x y : G, Commute x y := by
  classical
  intro x y
  by_cases hxy : x = y
  · subst hxy; exact Commute.refl x
  · have hcard : 1 < ({x, y} : Finset G).card := by rw [Finset.card_pair hxy]; omega
    rcases h1 {x, y} hcard with ⟨a, ha, b, hb, hab, hcab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hcab
    · exact hcab.symm
    · exact (hab rfl).elim

/-- If every subset of `G` of size greater than `2` contains a commuting pair, then `G` is
abelian, since any noncommuting pair `x, y` yields the pairwise noncommuting triple
`{x, y, x * y}`. -/
@[category API, AMS 20]
theorem commute_all_of_no_noncommuting_gt_two {G : Type*} [Group G]
    (h2 : HasNoPairwiseNoncommutingGt G 2) : ∀ x y : G, Commute x y := by
  classical
  intro x y
  by_contra hxy
  have hleft : ¬ Commute x (x * y) := by
    intro h
    apply hxy
    have h1 : x * (x * y) = x * (y * x) := by
      calc
        x * (x * y) = (x * y) * x := h
        _ = x * (y * x) := by rw [mul_assoc]
    exact mul_left_cancel h1
  have hright : ¬ Commute y (x * y) := by
    intro h
    apply hxy
    have h1 : (y * x) * y = (x * y) * y := by
      calc
        (y * x) * y = y * (x * y) := by rw [mul_assoc]
        _ = (x * y) * y := h
    exact (mul_right_cancel h1).symm
  have hxne : x ≠ y := fun h => hxy (h ▸ Commute.refl x)
  have hxmul : x ≠ x * y := fun h =>
    hxy ((mul_left_cancel (by simpa using h.symm : x * y = x * 1)) ▸ Commute.one_right x)
  have hymul : y ≠ x * y := fun h =>
    hxy ((mul_right_cancel (by simpa using h.symm : x * y = 1 * y)) ▸ Commute.one_left y)
  let s : Finset G := {x, y, x * y}
  have hcard : 2 < s.card := by
    have h1 : x ∉ ({y, x * y} : Finset G) := by simp [hxne, hxmul]
    have h2' : y ∉ ({x * y} : Finset G) := by simp [hymul]
    have hs : s.card = 3 := by simp [s, Finset.card_insert_of_notMem, h1, h2']
    omega
  rcases h2 s hcard with ⟨a, ha, b, hb, hab, hcab⟩
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact hab rfl
  · exact hxy hcab
  · exact hleft hcab
  · exact hxy hcab.symm
  · exact hab rfl
  · exact hright hcab
  · exact hleft hcab.symm
  · exact hright hcab.symm
  · exact hab rfl

/-- General pigeonhole lower bound: the cardinality of any pairwise noncommuting finite subset `S`
is at most the cardinality of any finite abelian subgroup cover `C` of `G`. -/
@[category API, AMS 20]
theorem card_noncommuting_le_abelianCover {G : Type*} [Group G]
    {S : Finset G} {C : Finset (Subgroup G)}
    (hS : IsPairwiseNoncommuting S) (hC : IsAbelianCover G C) :
    S.card ≤ C.card := by
  classical
  choose f hfC hfmem using hC.2
  refine Finset.card_le_card_of_injOn f (fun x _ => hfC x) ?_
  intro x hx y hy hfeq
  by_contra hxy
  exact hS x hx y hy hxy (hC.1 (f x) (hfC x) x (hfmem x) y (hfeq ▸ hfmem y))

/-- Exact base value `erdos117H 1 = 1`. -/
@[category test, AMS 20]
theorem erdos117H_one : erdos117H 1 = 1 := by
  have hmem : (1 : ℕ) ∈ {m : ℕ | ∀ (G : Type) [Group G], HasNoPairwiseNoncommutingGt G 1 →
      HasAbelianCoverOfCardLe G m} := fun G _ h1 =>
    hasAbelianCover_one_of_commute (commute_all_of_no_noncommuting_gt_one h1)
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨1, hmem⟩ ?_)
  intro m hm
  have htriv : HasNoPairwiseNoncommutingGt Unit 1 := by
    intro s hs
    have hle : s.card ≤ 1 := by
      calc
        s.card ≤ Fintype.card Unit := Finset.card_le_univ s
        _ = 1 := Fintype.card_unit
    omega
  rcases hm Unit htriv with ⟨C, hC, hCcard⟩
  exact le_trans (one_le_card_of_isAbelianCover hC) hCcard

/-- Exact base value `erdos117H 2 = 1`. -/
@[category test, AMS 20]
theorem erdos117H_two : erdos117H 2 = 1 := by
  have hmem : (1 : ℕ) ∈ {m : ℕ | ∀ (G : Type) [Group G], HasNoPairwiseNoncommutingGt G 2 →
      HasAbelianCoverOfCardLe G m} := fun G _ h2 =>
    hasAbelianCover_one_of_commute (commute_all_of_no_noncommuting_gt_two h2)
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨1, hmem⟩ ?_)
  intro m hm
  have htriv : HasNoPairwiseNoncommutingGt Unit 2 := by
    intro s hs
    have hle : s.card ≤ 1 := by
      calc
        s.card ≤ Fintype.card Unit := Finset.card_le_univ s
        _ = 1 := Fintype.card_unit
    omega
  rcases hm Unit htriv with ⟨C, hC, hCcard⟩
  exact le_trans (one_le_card_of_isAbelianCover hC) hCcard

/--
Let `h(n)` be minimal such that any group `G` in which every subset of size strictly greater than
`n` contains two distinct commuting elements can be covered by at most `h(n)` abelian subgroups.
Estimate `h(n)` as well as possible.

Pyber [Py87] proved exponential lower and upper bounds `c₁^n ≤ h(n) ≤ c₂^n` for `n ≥ 3`.
-/
@[category research solved, AMS 20]
theorem erdos_117 : ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ 1 < c₂ ∧
    ∀ n : ℕ, 3 ≤ n → c₁ ^ n ≤ (erdos117H n : ℝ) ∧ (erdos117H n : ℝ) ≤ c₂ ^ n := by
  sorry

/--
Lecomte [Le26] completely determined `h(n)` for all `n ≥ 9`:
`h(n) = 2 ^ ⌊(n - 1) / 2⌋ + 1`.
-/
@[category research solved, AMS 20]
theorem erdos_117.variants.lecomte_exact (n : ℕ) (hn : 9 ≤ n) :
    erdos117H n = 2 ^ ((n - 1) / 2) + 1 := by
  sorry

/--
Lecomte [Le26] also determined the exact small values of `h(n)`:
`h(n) = n` for `3 ≤ n ≤ 6`, and `h(7) = h(8) = 10`.
-/
@[category research solved, AMS 20]
theorem erdos_117.variants.lecomte_small :
    (∀ n : ℕ, 3 ≤ n → n ≤ 6 → erdos117H n = n) ∧ erdos117H 7 = 10 ∧ erdos117H 8 = 10 := by
  sorry

end Erdos117
