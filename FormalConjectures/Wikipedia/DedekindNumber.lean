/-
Copyright 2025 The Formal Conjectures Authors.

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
# Dedekind Numbers

A Dedekind number `M(n)` counts the number of monotone Boolean functions on `n` variables,
or equivalently, the number of antichains (Sperner families) in the Boolean lattice `2^[n]`.

For example,
$$M ( 0 ) = 2 , M ( 1 ) = 3 , M ( 2 ) = 6 , and M ( 3 ) = 20 .$$
The first few values grew slowly:
$$M ( 4 ) = 168 , M ( 5 ) = 7581$$,
but then rapidly:
$$M ( 6 ) = 7828354 , M ( 7 ) = 2414682040998 , M ( 8 ) = 56130437228687557907788$$, and
$$M ( 9 ) = 286386577668298411128469151667598498812366$$
(computed in 2023).

We formalize two definitions:
- `M n`: the number of monotone Boolean functions `(Fin n → Bool) → Bool`
- `M' n`: the number of antichains (Sperner families) of `Finset (Fin n)`

We prove their values for small `n` and show that the two definitions agree for all `n`.

The problem is to determine the exact values of $M(n)$ for $n ≥ 10$.
In particular, the value of $M(10)$ is currently unknown.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Dedekind_number)
- [Oeis/A372](https://oeis.org/A000372)

-/

namespace DedekindNumber

open Finset

instance piFinBoolDecidableLE {n : ℕ} :
DecidableRel (fun (a b : Fin n → Bool) => a ≤ b) :=
  fun a b => show Decidable (a ≤ b) from by
    rw [Pi.le_def]
    exact Fintype.decidableForallFintype

/-- $M(n)$ is the number of monotone Boolean functions on $n$ variables. -/
def M (n : ℕ) : ℕ :=
  Fintype.card {f : (Fin n → Bool) → Bool // Monotone f}

/-- A Sperner family (antichain) of subsets of `Fin n`: a family of sets such that
    no member is a subset of another. -/
def IsSperner {n : ℕ} (A : Finset (Finset (Fin n))) : Prop :=
  IsAntichain (fun s t => s ⊆ t) (A : Set (Finset (Fin n)))

instance isSpernerDecidable {n : ℕ} :
    DecidablePred (fun A : Finset (Finset (Fin n)) => IsSperner A) :=
  fun A => by
    unfold IsSperner IsAntichain Set.Pairwise
    simp only [Finset.mem_coe, Pi.compl_apply, compl_iff_not]
    exact inferInstance

/-- $M'(n)$ is the number of antichains (Sperner families) of subsets of `Fin n`. -/
def M' (n : ℕ) : ℕ :=
  Fintype.card {A : Finset (Finset (Fin n)) // IsSperner A}

/-- Values for small n -/
@[category test, AMS 5]
theorem M_zero : M 0 = 2 := by native_decide

@[category test, AMS 5]
theorem M_one : M 1 = 3 := by native_decide

@[category test, AMS 5]
theorem M_two : M 2 = 6 := by native_decide

@[category test, AMS 5]
theorem M_three : M 3 = 20 := by native_decide

@[category test, AMS 6]
theorem M'_zero : M' 0 = 2 := by native_decide

@[category test, AMS 6]
theorem M'_one : M' 1 = 3 := by native_decide

@[category test, AMS 6]
theorem M'_two : M' 2 = 6 := by native_decide

@[category test, AMS 6]
theorem M'_three : M' 3 = 20 := by native_decide

/-  ## Equivalence of M and M'
-/

/-- The indicator function of a finset: `χ s i = true ↔ i ∈ s`. -/
def χ {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

/-- The support of a Boolean-valued function: `supp v = {i | v i = true}`. -/
def supp {n : ℕ} (v : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun i => v i = true)

/-- Forward map: monotone function → Sperner family (the minimal true sets). -/
def toSperner {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Finset (Fin n)) :=
  univ.filter (fun s =>
    f (χ s) = true ∧ ∀ t : Finset (Fin n), t ⊆ s → f (χ t) = true → s ⊆ t)

/-- Backward map: Sperner family → monotone Boolean function. -/
def fromSperner {n : ℕ} (A : Finset (Finset (Fin n))) (v : Fin n → Bool) : Bool :=
  decide (∃ s ∈ A, ∀ i ∈ s, v i = true)

/-  ### Helper lemmas about χ and supp -/

@[category API, AMS 5]
lemma χ_supp {n : ℕ} (v : Fin n → Bool) : χ (supp v) = v := by
  funext i; simp [χ, supp]

@[category API, AMS 6]
lemma supp_χ {n : ℕ} (s : Finset (Fin n)) : supp (χ s) = s := by
  ext i
  simp [χ, supp]

@[category API, AMS 6]
lemma χ_le_iff {n : ℕ} (s t : Finset (Fin n)) : χ s ≤ χ t ↔ s ⊆ t := by
  constructor
  · intro h i hi
    contrapose! h
    exact fun H => by have := H i; simp_all +decide [ χ ]
  · intro h i; simp [χ];
    by_cases hi : i ∈ s <;> simp_all +decide [ Finset.subset_iff ]

@[category API, AMS 6]
lemma mem_supp_iff {n : ℕ} (v : Fin n → Bool) (i : Fin n) : i ∈ supp v ↔ v i = true := by
  simp [supp]

@[category API, AMS 6]
lemma toSperner_isSperner {n : ℕ} (f : (Fin n → Bool) → Bool) (_ : Monotone f) :
    IsSperner (toSperner f) := by
  intro s hs t ht hst; simp_all +decide [ Finset.ext_iff]
  contrapose! hst; unfold toSperner at *; aesop

@[category API, AMS 6]
lemma fromSperner_monotone {n : ℕ} (A : Finset (Finset (Fin n))) (_ : IsSperner A) :
    Monotone (fromSperner A) := by
      intro v w hvw hfv
      obtain ⟨s, hsA, hs⟩ : ∃ s ∈ A, s ⊆ supp v := by
        unfold fromSperner at hfv
        simp_all +decide [ Finset.subset_iff, mem_supp_iff ]
      have hs_w : s ⊆ supp w := by
        intro i hi; have := hs hi
        simp_all +decide [ Finset.subset_iff, mem_supp_iff ]
        exact Bool.eq_false_imp_eq_true.mp fun a ↦ hvw i (hs hi)
      exact decide_eq_true
        ( ⟨ s, hsA, fun i hi => by simpa using Finset.mem_filter.mp ( hs_w hi ) |>.2 ⟩ )

@[category graduate, AMS 5 6]
lemma exists_minimal_true_subset {n : ℕ} {f : (Fin n → Bool) → Bool} (_ : Monotone f)
    {s : Finset (Fin n)} (hs : f (χ s) = true) :
    ∃ t, t ⊆ s ∧ f (χ t) = true ∧ ∀ u, u ⊆ t → f (χ u) = true → t ⊆ u := by
      obtain ⟨t, ht₁, ht₂⟩ :
        ∃ t ∈ {t : Finset (Fin n) | t ⊆ s ∧ f (χ t) = true},
        ∀ u ∈ {t : Finset (Fin n) | t ⊆ s ∧ f (χ t) = true}, t.card ≤ u.card := by
        apply_rules [ Set.exists_min_image ]
        · exact Set.finite_iff_bddAbove.mpr ⟨ s, fun t ht => ht.1 ⟩
        · exact ⟨ s, Finset.Subset.refl _, hs ⟩
      refine' ⟨ t, ht₁.1, ht₁.2, fun u hu hu' => _ ⟩
      exact Classical.not_not.1 fun h =>
        not_lt_of_ge ( ht₂ u ⟨ hu.trans ht₁.1, hu' ⟩ )
        ( Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.2 ⟨ hu, by aesop ⟩ )

@[category graduate, AMS 5 6]
lemma fromSperner_toSperner {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    fromSperner (toSperner f) = f := by
  funext v
  by_cases h : f v <;> simp_all +decide [ fromSperner ]
  · obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Finset (Fin n),
    t ⊆ Finset.univ.filter (fun i => v i = true) ∧
    f (χ t) = true ∧
    ∀ u : Finset (Fin n), u ⊆ t → f (χ u) = true → t ⊆ u := by
      apply exists_minimal_true_subset hf;
      convert h using 2
      exact funext fun i => by unfold χ; aesop;
    exact ⟨ t, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ht₂.1, ht₂.2 ⟩,
    fun i hi => Finset.mem_filter.mp ( ht₁ hi ) |>.2 ⟩
  · intro s hs; contrapose! h; simp_all +decide [ toSperner ]
    refine' hf _ hs.1
    intro i; by_cases hi : i ∈ s <;> simp_all +decide [ χ ]

@[category graduate, AMS 5 6]
lemma toSperner_fromSperner {n : ℕ} (A : Finset (Finset (Fin n))) (hA : IsSperner A) :
    toSperner (fromSperner A) = A := by
  ext s; simp [toSperner, fromSperner]
  constructor <;> intro hs
  all_goals generalize_proofs at *
  · obtain ⟨ ⟨ t, ht₁, ht₂ ⟩, ht₃ ⟩ := hs
    convert ht₁ using 1
    exact subset_antisymm ( ht₃ t ( by unfold χ at ht₂; aesop ) t ht₁ ( by unfold χ; aesop ) )
      ( by unfold χ at ht₂; aesop )
  · refine' ⟨ ⟨ s, hs, _ ⟩, _ ⟩ <;> simp_all +decide [ IsSperner ]
    · exact fun i hi => by unfold χ; aesop
    · intro t ht x hx hx'; have := hA hx hs; simp_all +decide [ Finset.subset_iff, χ ]
/--
  The set of monotone Boolean functions on `n` variables is in bijection
  with the set of Sperner families of subsets of `Fin n`.
-/
def equivMonotoneSperner (n : ℕ) :
    {f : (Fin n → Bool) → Bool // Monotone f} ≃
    {A : Finset (Finset (Fin n)) // IsSperner A} where
  toFun := fun ⟨f, hf⟩ => ⟨toSperner f, toSperner_isSperner f hf⟩
  invFun := fun ⟨A, hA⟩ => ⟨fromSperner A, fromSperner_monotone A hA⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.ext (fromSperner_toSperner f hf)
  right_inv := fun ⟨A, hA⟩ => Subtype.ext (toSperner_fromSperner A hA)

@[category test, AMS 5 6]
theorem M_eq_M' : M  = M' := by
  ext n
  exact Fintype.card_congr (equivMonotoneSperner n)

/--
  No closed form for the Dedekind numbers are currently unknown.
-/
@[category research open, AMS 5 6]
theorem DedekindNumbers : M = answer(sorry) := by
  sorry

/--
  In particular, the Dedekind number for `n = 10` is currently unknown.
-/
@[category research open, AMS 5 6]
theorem Dedekind_10 : M 10 = answer(sorry) := by sorry

end DedekindNumber
