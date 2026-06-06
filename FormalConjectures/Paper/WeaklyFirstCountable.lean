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
# Conjectures about Weakly First Countable spaces

This file formalizes the notion of a weakly first countable topological space and some conjectures
around those.

*References:*
* [Ar2013] Arhangeliski, Alexandr. "Selected old open problems in general topology."
  Buletinul Academiei de Ştiinţe a Republicii Moldova. Matematica 73.2-3 (2013): 37-46.
  https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf
* [Ya1976] Yakovlev, N. N. "On the theory of o-metrizable spaces."
  Doklady Akademii Nauk. Vol. 229. No. 6. Russian Academy of Sciences, 1976.
  https://www.mathnet.ru/links/016f74007f9f96fa3aadae05cbd98457/dan40570.pdf (in Russian)
-/

open TopologicalSpace Topology Filter
open scoped Cardinal

namespace WeaklyFirstCountable

/-- A topological space $X$ is called *weakly first countable* if there exists a function
$N : X → ℕ → Set X, such that:

* For all $x : X, n : ℕ$ we have $x ∈ V x n$
* For all $x : X, n : ℕ$: $V x (n + 1) ⊆ V x n$
* $O ⊆ X$ is open iff $∀ x ∈ O, ∃ n : ℕ, V x n ⊆ O$
-/
class WeaklyFirstCountableTopology (X : Type*) [TopologicalSpace X] : Prop where
  nhds_countable_weak_basis :
    ∃ V : X → ℕ → Set X,
      (∀ (x : X), Antitone (V x) ∧ ∀ (n : ℕ), x ∈ V x n) ∧
        ∀ O : Set X, IsOpen O ↔ ∀ x ∈ O, ∃ k : ℕ, V x k ⊆ O

/-- There are weakly first countable spaces which are not first countable,
for example the [Arens Space](https://topology.pi-base.org/spaces/S000156). -/
@[category textbook, AMS 54]
theorem exists_weakly_first_countable_not_first_countable : ∃ (X : Type) (_ : TopologicalSpace X),
      WeaklyFirstCountableTopology X ∧ ¬ FirstCountableTopology X := by sorry

/-- Every first countable space is weakly first countable,
simply take $N x$ as a countable neighborhood basis of $x$. -/
@[category test, AMS 54]
instance FirstCountableTopology.weaklyFirstCountableTopology (X : Type*) [TopologicalSpace X]
    [FirstCountableTopology X] : WeaklyFirstCountableTopology X := by
  have has_basis: ∀ a : X, ∃ x : ℕ → Set X, (𝓝 a).HasAntitoneBasis x := by
    intro a
    rw [← Filter.isCountablyGenerated_iff_exists_antitone_basis]
    exact FirstCountableTopology.nhds_generated_countable a
  let U : X → ℕ → Set X := fun x ↦ (has_basis x).choose
  have hU : ∀ x, (𝓝 x).HasAntitoneBasis (U x) :=
    fun x ↦ Exists.choose_spec (has_basis x)
  use U
  constructor
  · exact fun x ↦ ⟨(hU x).antitone, fun n ↦ mem_of_mem_nhds (HasAntitoneBasis.mem (hU x) n)⟩
  intro O
  rw [isOpen_iff_mem_nhds]
  constructor <;> intro h x hx
  · exact (HasAntitoneBasis.mem_iff (hU x)).mp (h x hx)
  · obtain ⟨n, hn⟩ := h x hx
    exact mem_of_superset (HasAntitoneBasis.mem (hU x) n) hn

/-- Problem 2 in [Ar2013]: Give an example in ZFC of a weakly first-
countable compact space X such that $𝔠 < |X|$. -/
@[category research solved, AMS 54]
theorem existsWeaklyFirstCountableCompactBig : answer(True) ↔
    ∃ (X : Type) (_ : TopologicalSpace X),
      WeaklyFirstCountableTopology X ∧ CompactSpace X ∧ 𝔠 < #X :=
  /- We can just take `X = Set ℝ` with the indiscrete topology.
  By the previous lemmas, it is weakly first countable and compact.
  Its cardinality is `2^𝔠`, which is strictly greater than `𝔠` by Cantor's theorem. -/
  by
  constructor
  · intro _
    use Set ℝ, ⊤
    refine ⟨?_, ?_, ?_⟩
    · letI : TopologicalSpace (Set ℝ) := ⊤
      exact ⟨fun _ _ ↦ Set.univ, fun x ↦ ⟨fun _ _ _ ↦ Set.Subset.rfl, fun _ ↦ trivial⟩, fun O ↦ by
        rw [TopologicalSpace.isOpen_top_iff]
        constructor
        · rintro (rfl | rfl)
          · intro x hx; exact hx.elim
          · intro x _
            exact ⟨0, Set.Subset.rfl⟩
        · intro h
          by_cases hO : O = ∅
          · exact Or.inl hO
          · right
            ext x
            simp only [Set.mem_univ, iff_true]
            have hO_nonempty : O.Nonempty := Set.nonempty_iff_ne_empty.mpr hO
            obtain ⟨y, hy⟩ := hO_nonempty
            obtain ⟨k, hk⟩ := h y hy
            exact hk (Set.mem_univ x)⟩
    · letI : TopologicalSpace (Set ℝ) := ⊤
      exact ⟨by
        rw [isCompact_iff_finite_subcover]
        intro ι U hUo hU
        cases isEmpty_or_nonempty (Set ℝ)
        · exact ⟨∅, by simp [Set.univ_eq_empty_iff.mpr ‹_›]⟩
        · obtain ⟨x⟩ := ‹Nonempty (Set ℝ)›
          have hxU : x ∈ ⋃ i, U i := hU (Set.mem_univ x)
          simp only [Set.mem_iUnion] at hxU
          obtain ⟨i, hi⟩ := hxU
          have hUi : U i = Set.univ := by
            have := hUo i
            rw [TopologicalSpace.isOpen_top_iff] at this
            rcases this with h | h
            · rw [h] at hi; exact hi.elim
            · exact h
          exact ⟨{i}, by simp [hUi]⟩⟩
    · have h1 : #(Set ℝ) = 2 ^ #ℝ := Cardinal.mk_set
      have h2 : #ℝ = 𝔠 := Cardinal.mk_real
      rw [h1, h2]
      exact Cardinal.cantor 𝔠
  · intro _
    trivial

/-- Problem 3 in [Ar2013]: Give an example in ZFC of a weakly first-
countable compact space which is not first countable. -/
def ExistsWeaklyFirstCountableCompactNotFirstCountable : Prop :=
    ∃ (X : Type) (_ : TopologicalSpace X), WeaklyFirstCountableTopology X ∧ CompactSpace X ∧
      ¬ FirstCountableTopology X

/-
We construct a countable space `X` which is weakly first countable,
compact, and not first countable. The space `X` is defined as a
disjoint union of a point `zero`, a point `star`, a sequence of
points `x n`, and a double sequence of points `y n m` for
$n, m ∈ ℕ$.

The topology is defined by specifying the weak neighborhood
basis `V(p, k)`:

* `V(y n m, k) = {y n m}`
* `V(x n, k) = {x n} ∪ {y n m | m ≥ k}`
* `V(zero, k) = {zero} ∪ {x n | n ≥ k}`
* `V(star, k) = Set.univ`

A set `O` is defined to be open if for all `p ∈ O`, there exists
`k` such that `V p k ⊆ O`. This automatically defines a weakly
first countable topology.

**Compactness:** Any open set `O` containing `star` must contain
`V star k` for some `k`. But `V star k = Set.univ`, so the cover
is trivially finite.

**Not first countable:** The point `zero` does not have a countable
neighborhood basis. If `B i` were a countable neighborhood basis,
each `B i` would contain some `V zero (k i)`, and for each
`n ≥ k i`, it would contain `V (x n) (m i)`. We can construct an
open set `O` containing `zero` that does not contain any `B i` by
choosing `O` to exclude `y (n i) (m i)` for a suitably chosen
sequence. This diagonal argument shows that no countable family of
neighborhoods can form a basis at `zero`.
-/

open TopologicalSpace Topology Filter Set

inductive X
| zero : X
| x (n : ℕ) : X
| y (n m : ℕ) : X
| star : X
def V : X → ℕ → Set X
| X.zero, k => {X.zero} ∪ {X.x n | n ≥ k}
| X.x n, k => {X.x n} ∪ {X.y n m | m ≥ k}
| X.y n m, _ => {X.y n m}
| X.star, _ => Set.univ
def X_isOpen (O : Set X) : Prop :=
  ∀ p ∈ O, ∃ k, V p k ⊆ O

@[category API, AMS 54]
lemma X_isOpen_univ : X_isOpen Set.univ := by
  intro p _
  use 0
  exact subset_univ _
@[category API, AMS 54]
lemma X_isOpen_inter (s t : Set X) (hs : X_isOpen s) (ht : X_isOpen t) :
    X_isOpen (s ∩ t) := by
  intro p hp
  rcases hs p hp.1 with ⟨k1, hk1⟩
  rcases ht p hp.2 with ⟨k2, hk2⟩
  use max k1 k2
  intro q hq
  have H : ∀ k1 k2, k1 ≤ k2 → V p k2 ⊆ V p k1 := by
    intro k1 k2 hk
    cases p
    · intro q hq
      simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq] at hq ⊢
      rcases hq with rfl | ⟨n, hn, rfl⟩
      · left; rfl
      · right; use n; exact ⟨le_trans hk hn, rfl⟩
    · intro q hq
      simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq] at hq ⊢
      rcases hq with rfl | ⟨m, hm, rfl⟩
      · left; rfl
      · right; use m; exact ⟨le_trans hk hm, rfl⟩
    · intro q hq
      exact hq
    · intro q hq
      exact hq
  constructor
  · apply hk1
    apply H k1 (max k1 k2) (le_max_left _ _) hq
  · apply hk2
    apply H k2 (max k1 k2) (le_max_right _ _) hq
@[category API, AMS 54]
lemma X_isOpen_sUnion (s : Set (Set X)) (hs : ∀ t ∈ s, X_isOpen t) :
    X_isOpen (⋃₀ s) := by
  intro p hp
  rcases hp with ⟨t, ht, hp⟩
  rcases hs t ht p hp with ⟨k, hk⟩
  use k
  exact subset_sUnion_of_subset s t hk ht
instance : TopologicalSpace X where
  IsOpen := X_isOpen
  isOpen_univ := X_isOpen_univ
  isOpen_inter := X_isOpen_inter
  isOpen_sUnion := X_isOpen_sUnion
@[category API, AMS 54]
lemma X_compact : CompactSpace X := by
  constructor
  rw [isCompact_iff_finite_subcover]
  intro ι U hU hcov
  have hstar : X.star ∈ ⋃ i, U i := hcov (mem_univ X.star)
  rcases mem_iUnion.mp hstar with ⟨i, hi⟩
  have hopen := hU i
  have hV : ∃ k, V X.star k ⊆ U i := hopen X.star hi
  rcases hV with ⟨k, hk⟩
  have h_univ : Set.univ ⊆ U i := by
    have : V X.star k = Set.univ := rfl
    rw [← this]
    exact hk
  use {i}
  intro p _
  simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
  exact h_univ (mem_univ p)
@[category API, AMS 54]
lemma X_not_firstCountable : ¬ FirstCountableTopology X := by
  intro h
  have has_basis : ∃ B : ℕ → Set X, (𝓝 X.zero).HasAntitoneBasis B := by
    rw [← Filter.isCountablyGenerated_iff_exists_antitone_basis]
    exact FirstCountableTopology.nhds_generated_countable X.zero
  rcases has_basis with ⟨B, hB⟩
  have h_Ui : ∀ i, ∃ U, IsOpen U ∧ X.zero ∈ U ∧ U ⊆ B i := by
    intro i
    have hBi : B i ∈ 𝓝 X.zero := hB.toHasBasis.mem_of_mem trivial
    rcases mem_nhds_iff.mp hBi with ⟨t, ht_sub, ht_open, ht_zero⟩
    exact ⟨t, ht_open, ht_zero, ht_sub⟩
  choose U hU_open hU_zero hU_B using h_Ui
  have h_k : ∀ i, ∃ k, V X.zero k ⊆ U i := fun i => hU_open i X.zero (hU_zero i)
  choose k hk using h_k
  have h_n : ∀ i, ∃ n, n = max i (k i) := fun i => ⟨max i (k i), rfl⟩
  choose n hn using h_n
  have h_x_in_U : ∀ i, X.x (n i) ∈ U i := by
    intro i
    apply hk i
    simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq]
    right
    use n i
    refine ⟨?_, rfl⟩
    rw [hn i]
    exact le_max_right i (k i)
  have h_m : ∀ i, ∃ m, V (X.x (n i)) m ⊆ U i := fun i => hU_open i (X.x (n i)) (h_x_in_U i)
  choose m hm using h_m
  have h_y_in_U : ∀ i, X.y (n i) (m i) ∈ U i := by
    intro i
    apply hm i
    simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq]
    right
    use m i
  have h_y_in_B : ∀ i, X.y (n i) (m i) ∈ B i := fun i => hU_B i (h_y_in_U i)
  let M (n' : ℕ) : ℕ := (Finset.filter (fun j => n j = n') (Finset.range (n' + 1))).sup m + 1
  let O : Set X := Set.univ \ ({X.star} ∪ {X.y (n i) (m i) | i : ℕ})
  have hO_open : IsOpen O := by
    intro p hp
    cases p
    · use 0
      intro q hq
      simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq] at hq
      rcases hq with rfl | ⟨n', hn', rfl⟩
      · exact hp
      · simp only [O, mem_diff, mem_univ, mem_union, mem_singleton_iff, mem_setOf_eq, true_and, not_or]
        constructor
        · intro h_eq; contradiction
        · intro h_eq
          rcases h_eq with ⟨i, hi⟩
          contradiction
    · rename_i n'
      use M n'
      intro q hq
      simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq] at hq
      rcases hq with rfl | ⟨m', hm', rfl⟩
      · exact hp
      · simp only [O, mem_diff, mem_univ, mem_union, mem_singleton_iff, mem_setOf_eq, true_and, not_or]
        constructor
        · intro h_eq; contradiction
        · intro h_eq
          rcases h_eq with ⟨i, hi⟩
          have h_eq_n : n i = n' := by injection hi
          have h_eq_m : m i = m' := by injection hi
          have hn_le : i ≤ n i := by
            rw [hn i]
            exact le_max_left i (k i)
          have hm_lt : m i < M n' := by
            have h1 : i ∈ Finset.filter (fun j => n j = n') (Finset.range (n' + 1)) := by
              rw [Finset.mem_filter, Finset.mem_range]
              refine ⟨?_, h_eq_n⟩
              omega
            have h2 := Finset.le_sup (f := m) h1
            exact Nat.lt_add_one_iff.mpr h2
          omega
    · rename_i n' m'
      use 0
      intro q hq
      simp only [V, mem_singleton_iff] at hq
      rcases hq with rfl
      exact hp
    · simp only [O, mem_diff, mem_univ, mem_union, mem_singleton_iff, mem_setOf_eq, true_and, not_or] at hp
      rcases hp with ⟨hp1, hp2⟩
      contradiction
  have hO_zero : X.zero ∈ O := by
    simp [O]
  have hO_nhd : O ∈ 𝓝 X.zero := IsOpen.mem_nhds hO_open hO_zero
  have hB_O : ∃ i, B i ⊆ O := by
    rcases (HasBasis.mem_iff hB.toHasBasis).mp hO_nhd with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  rcases hB_O with ⟨i, hi⟩
  have h_y_in_O : X.y (n i) (m i) ∈ O := hi (h_y_in_B i)
  simp only [O, mem_diff, mem_univ, mem_union, mem_singleton_iff, mem_setOf_eq, true_and, not_or] at h_y_in_O
  rcases h_y_in_O with ⟨_, h_y⟩
  apply h_y
  use i

/-- Problem 3 in [Ar2013]: Give an example in ZFC of a weakly first-
countable compact space which is not first countable. -/
@[category research solved, AMS 54]
theorem existsWeaklyFirstCountableCompactNotFirstCountable :
    ExistsWeaklyFirstCountableCompactNotFirstCountable := by
  use X, inferInstance
  constructor
  · constructor
    use V
    constructor
    · intro p
      constructor
      · intro k1 k2 hk q hq
        cases p
        · simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq] at hq ⊢
          rcases hq with rfl | ⟨n, hn, rfl⟩
          · left; rfl
          · right; use n; exact ⟨le_trans hk hn, rfl⟩
        · simp only [V, mem_union, mem_singleton_iff, mem_setOf_eq] at hq ⊢
          rcases hq with rfl | ⟨m, hm, rfl⟩
          · left; rfl
          · right; use m; exact ⟨le_trans hk hm, rfl⟩
        · exact hq
        · exact hq
      · intro k
        cases p
        · simp [V]
        · simp [V]
        · simp [V]
        · simp [V]
    · intro O
      rfl
  · exact ⟨X_compact, X_not_firstCountable⟩

/-- Under CH, such a space exists as constructed in [Ya1976] by Yakovlev. -/
@[category research solved, AMS 54]
theorem CH.existsWeaklyFirstCountableCompactNotFirstCountable [Fact (ℵ₁ = 𝔠)] :
    ExistsWeaklyFirstCountableCompactNotFirstCountable := by sorry

-- TODO: add Problem 4 in [Ar2013]

end WeaklyFirstCountable
