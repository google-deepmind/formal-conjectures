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
# Erdős Problem 338

*References:*
- [erdosproblems.com/338](https://www.erdosproblems.com/338)
- [Pa33] Pall, Gordon, *On Sums of Squares*. Amer. Math. Monthly (1933), 10-18.
- [Forum example](https://www.erdosproblems.com/forum/thread/338#post-8488),
  BitterLemma, 17 August 2026, citing Patrick White's working report of 28 July 2026.
-/

@[expose] public section

namespace Erdos338

open Filter

/-- `A` is an additive basis of order (at most) `h`: every sufficiently large natural number is
the sum of at most `h` elements of `A`, repetitions allowed. -/
def IsAddBasisOfOrderLE (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Multiset ℕ, (∀ a ∈ s, a ∈ A) ∧ Multiset.card s ≤ h ∧ s.sum = n

/-- `A` is an additive basis (of some finite order). -/
def IsAddBasis (A : Set ℕ) : Prop := ∃ h, IsAddBasisOfOrderLE A h

/-- `h` is *the* order of `A`: `A` is a basis of order `h` and of no smaller order. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAddBasisOfOrderLE A h ∧ ∀ k < h, ¬ IsAddBasisOfOrderLE A k

/-- Every sufficiently large natural number is the sum of at most `t` *distinct* elements
of `A`. -/
def IsRestrictedBasisOfOrderLE (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ s.card ≤ t ∧ ∑ a ∈ s, a = n

/-- `t` is the restricted order of `A` (the least `t` with the property above). -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  IsRestrictedBasisOfOrderLE A t ∧ ∀ k < t, ¬ IsRestrictedBasisOfOrderLE A k

/-- The restricted order of `A` exists. -/
def HasSomeRestrictedOrder (A : Set ℕ) : Prop := ∃ t, IsRestrictedBasisOfOrderLE A t

/-- Question 2 of #338: can the restricted order be bounded (when it exists) in terms of the
order? I.e. is there `F : ℕ → ℕ` such that every basis of order `h` that has a restricted order
`t` satisfies `t ≤ F h`? -/
def RestrictedOrderBoundedByOrder : Prop :=
  ∃ F : ℕ → ℕ, ∀ (A : Set ℕ) (h t : ℕ), HasOrder A h → HasRestrictedOrder A t → t ≤ F h

/-- Sub-question of #338: if `A \ F` is a basis for every finite `F`, must `A` have a
restricted order? -/
def CofiniteBasisImpliesRestrictedOrder : Prop :=
  ∀ A : Set ℕ, (∀ F : Finset ℕ, IsAddBasis (A \ ↑F)) → HasSomeRestrictedOrder A

/-- Sub-question of #338: same as above, assuming moreover that all the bases `A \ F`
(`F` finite) have the same order `h`. -/
def CofiniteSameOrderBasisImpliesRestrictedOrder : Prop :=
  ∀ (A : Set ℕ) (h : ℕ), (∀ F : Finset ℕ, HasOrder (A \ ↑F) h) → HasSomeRestrictedOrder A

/-- The restricted order of a basis is the least integer $t$ (if it exists) such that every
large integer is the sum of at most $t$ distinct summands from $A$. What are necessary and
sufficient conditions that this exists? -/
@[category research open, AMS 5 11]
theorem erdos_338.parts.i :
    {A : Set ℕ | IsAddBasis A ∧ HasSomeRestrictedOrder A} = answer(sorry) := by
  sorry

/-- Can the restricted order be bounded (when it exists) in terms of the order of the basis? -/
@[category research open, AMS 5 11]
theorem erdos_338.parts.ii : answer(sorry) ↔ RestrictedOrderBoundedByOrder := by
  sorry

/-- What are necessary and sufficient conditions that the restricted order is equal to the
order of the basis? -/
@[category research open, AMS 5 11]
theorem erdos_338.parts.iii :
    {A : Set ℕ | IsAddBasis A ∧ ∃ h, HasOrder A h ∧ HasRestrictedOrder A h} =
      answer(sorry) := by
  sorry

/-- Is it true that if $A \setminus F$ is a basis for all finite sets $F$ then $A$ must have
a restricted order? -/
@[category research open, AMS 5 11]
theorem erdos_338.variants.finite_removal :
    answer(sorry) ↔ CofiniteBasisImpliesRestrictedOrder := by
  sorry

/-- What if the sets $A \setminus F$ are all bases of the same order? -/
@[category research open, AMS 5 11]
theorem erdos_338.variants.same_order_finite_removal :
    answer(sorry) ↔ CofiniteSameOrderBasisImpliesRestrictedOrder := by
  sorry

@[category API, AMS 5 11]
theorem IsAddBasisOfOrderLE.mono {A : Set ℕ} {h k : ℕ} (hA : IsAddBasisOfOrderLE A h)
    (hk : h ≤ k) : IsAddBasisOfOrderLE A k :=
  Filter.Eventually.mono hA fun _ ⟨s, hs, hc, hsum⟩ => ⟨s, hs, hc.trans hk, hsum⟩

@[category API, AMS 5 11]
theorem IsRestrictedBasisOfOrderLE.mono {A : Set ℕ} {t k : ℕ}
    (hA : IsRestrictedBasisOfOrderLE A t) (hk : t ≤ k) : IsRestrictedBasisOfOrderLE A k :=
  Filter.Eventually.mono hA fun _ ⟨s, hs, hc, hsum⟩ => ⟨s, hs, hc.trans hk, hsum⟩

/-- A sum of at most `t` distinct elements is in particular a sum of at most `t` elements. -/
@[category API, AMS 5 11]
theorem IsRestrictedBasisOfOrderLE.isAddBasisOfOrderLE {A : Set ℕ} {t : ℕ}
    (hA : IsRestrictedBasisOfOrderLE A t) : IsAddBasisOfOrderLE A t :=
  Filter.Eventually.mono hA fun _ ⟨s, hs, hc, hsum⟩ =>
    ⟨s.val, fun a ha => hs ha, by simpa using hc, by rw [← hsum, Finset.sum_eq_multiset_sum, Multiset.map_id']⟩

/-- If both exist, the restricted order is at least the order. -/
@[category API, AMS 5 11]
theorem order_le_restrictedOrder {A : Set ℕ} {h t : ℕ} (hh : HasOrder A h)
    (ht : HasRestrictedOrder A t) : h ≤ t := by
  by_contra hlt
  exact hh.2 t (by omega) ht.1.isAddBasisOfOrderLE

/-- Bateman's set `{1} ∪ {x > 0 : h ∣ x}`. -/
def batemanSet (h : ℕ) : Set ℕ := {x | x = 1 ∨ (0 < x ∧ h ∣ x)}

/-- Multisets from Bateman's set: `sum = (#ones) + h * m`, and if `m ≠ 0` then some element
is not `1`. -/
@[category API, AMS 5 11]
lemma bateman_multiset_sum {h : ℕ} (hh : 2 ≤ h) (s : Multiset ℕ)
    (hs : ∀ a ∈ s, a ∈ batemanSet h) :
    ∃ m, s.sum = s.count 1 + h * m ∧ (m = 0 ∨ s.count 1 < Multiset.card s) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨m, hm, hm'⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    have ha := hs a (Multiset.mem_cons_self a s)
    have hcs : s.count 1 ≤ Multiset.card s := Multiset.count_le_card 1 s
    rcases ha with rfl | ⟨hpos, k, rfl⟩
    · refine ⟨m, ?_, ?_⟩
      · simp [hm]; ring
      · simp; omega
    · have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
      have hne : (1 : ℕ) ≠ h * k := by nlinarith
      refine ⟨m + k, ?_, ?_⟩
      · rw [Multiset.sum_cons, Multiset.count_cons_of_ne hne, hm]; ring
      · right; rw [Multiset.count_cons_of_ne hne, Multiset.card_cons]; omega

@[category API, AMS 5 11]
theorem batemanSet_isAddBasisOfOrderLE {h : ℕ} (hh : 1 ≤ h) :
    IsAddBasisOfOrderLE (batemanSet h) h := by
  refine Filter.eventually_atTop.2 ⟨h, fun n hn => ?_⟩
  refine ⟨(h * (n / h)) ::ₘ Multiset.replicate (n % h) 1, ?_, ?_, ?_⟩
  · intro a ha
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · right
      refine ⟨?_, dvd_mul_right _ _⟩
      have : 1 ≤ n / h := (Nat.one_le_div_iff (by omega)).2 hn
      positivity
    · left; exact Multiset.eq_of_mem_replicate ha
  · simp only [Multiset.card_cons, Multiset.card_replicate]
    have := Nat.mod_lt n (show 0 < h by omega)
    omega
  · simp [Nat.div_add_mod]

@[category API, AMS 5 11]
theorem batemanSet_not_isAddBasisOfOrderLE {h : ℕ} (hh : 2 ≤ h) :
    ¬ IsAddBasisOfOrderLE (batemanSet h) (h - 1) := by
  intro hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  obtain ⟨s, hs, hcard, hsum⟩ := hN (h * (N + 1) + (h - 1)) (by nlinarith)
  obtain ⟨m, hm, hm'⟩ := bateman_multiset_sum hh s hs
  have hc : s.count 1 ≤ Multiset.card s := Multiset.count_le_card 1 s
  rcases hm' with rfl | hlt
  · nlinarith
  · have h1 := congrArg (· % h) (hm.symm.trans hsum)
    have e1 : (s.count 1 + h * m) % h = s.count 1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (h * (N + 1) + (h - 1)) % h = h - 1 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    simp only [e1, e2] at h1
    omega

/-- For `h ≥ 2`, Bateman's set has order exactly `h`. -/
@[category API, AMS 5 11]
theorem batemanSet_hasOrder {h : ℕ} (hh : 2 ≤ h) : HasOrder (batemanSet h) h :=
  ⟨batemanSet_isAddBasisOfOrderLE (by omega), fun k hk hA =>
    batemanSet_not_isAddBasisOfOrderLE hh (hA.mono (by omega))⟩

/-- Sums of distinct elements of Bateman's set are `≡ 0` or `≡ 1` modulo `h`. -/
@[category API, AMS 5 11]
lemma bateman_finset_sum_mod {h : ℕ} (hh : 2 ≤ h) (s : Finset ℕ)
    (hs : (↑s : Set ℕ) ⊆ batemanSet h) :
    (∑ a ∈ s, a) % h = if 1 ∈ s then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.coe_insert, Set.insert_subset_iff] at hs
    rw [Finset.sum_insert has]
    rcases hs.1 with rfl | ⟨hpos, k, rfl⟩
    · have : (1 : ℕ) ∉ s := has
      rw [Nat.add_mod, ih hs.2]
      simp [this, Nat.mod_eq_of_lt (show 1 < h by omega)]
    · have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
      have hne : (1 : ℕ) ≠ h * k := by nlinarith
      rw [Nat.mul_add_mod, ih hs.2]
      simp [Finset.mem_insert, hne]

/-- For `h ≥ 3`, Bateman's set has no restricted order: integers `≡ 2 (mod h)` are never sums of
distinct elements. -/
@[category API, AMS 5 11]
theorem batemanSet_not_hasSomeRestrictedOrder {h : ℕ} (hh : 3 ≤ h) :
    ¬ HasSomeRestrictedOrder (batemanSet h) := by
  rintro ⟨t, ht⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ht
  obtain ⟨s, hs, -, hsum⟩ := hN (h * N + 2) (by nlinarith)
  have := bateman_finset_sum_mod (by omega) s hs
  rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 2 < h)] at this
  split_ifs at this; omega

/-- **Bateman's example** (Erdős #338): for every `h ≥ 3`, `{1} ∪ {x > 0 : h ∣ x}` is a basis of
order exactly `h` with no restricted order. -/
@[category research solved, AMS 5 11]
theorem erdos_338.variants.bateman {h : ℕ} (hh : 3 ≤ h) :
    HasOrder (batemanSet h) h ∧ ¬ HasSomeRestrictedOrder (batemanSet h) :=
  ⟨batemanSet_hasOrder (by omega), batemanSet_not_hasSomeRestrictedOrder hh⟩

/-- `{4, 6} ∪ {10q : q ≥ 1} ∪ {10q + 3 : q ≥ 1}`. -/
def forumSet : Set ℕ :=
  {n | n = 4 ∨ n = 6 ∨ (n % 10 = 0 ∧ 10 ≤ n) ∨ (n % 10 = 3 ∧ 13 ≤ n)}

@[category API, AMS 5 11]
lemma exists_finset_of_list {A : Set ℕ} {t n : ℕ} (l : List ℕ) (hl : l.Nodup)
    (hA : ∀ a ∈ l, a ∈ A) (ht : l.length ≤ t) (hn : l.sum = n) :
    ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ s.card ≤ t ∧ ∑ a ∈ s, a = n := by
  refine ⟨l.toFinset, fun a ha => hA a (by simpa using ha), ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hl]; exact ht
  · rw [List.sum_toFinset _ hl]; simpa using hn

@[category API, AMS 5 11]
theorem forumSet_isAddBasisOfOrderLE_three : IsAddBasisOfOrderLE forumSet 3 := by
  refine Filter.eventually_atTop.2 ⟨30, fun n hn => ?_⟩
  have hr := Nat.mod_lt n (show 10 > 0 by norm_num)
  interval_cases hm : n % 10
  · exact ⟨{n}, by simp [forumSet]; omega, by simp, by simp⟩
  · exact ⟨{4, 4, n - 8}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{6, 6, n - 12}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{n}, by simp [forumSet]; omega, by simp, by simp⟩
  · exact ⟨{4, n - 4}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{6, 6, n - 12}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{6, n - 6}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{4, n - 4}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{4, 4, n - 8}, by simp [forumSet]; omega, by simp, by simp; omega⟩
  · exact ⟨{6, n - 6}, by simp [forumSet]; omega, by simp, by simp; omega⟩

/-- No integer `≡ 1 (mod 10)` is a sum of at most two elements of `forumSet`. -/
@[category API, AMS 5 11]
theorem forumSet_not_isAddBasisOfOrderLE_two : ¬ IsAddBasisOfOrderLE forumSet 2 := by
  intro hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  obtain ⟨s, hs, hc, h⟩ := hN (10 * N + 1) (by omega)
  have : Multiset.card s = 0 ∨ Multiset.card s = 1 ∨ Multiset.card s = 2 := by omega
  rcases this with hk | hk | hk
  · rw [Multiset.card_eq_zero] at hk; subst hk; simp at h
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hk
    have := hs a (by simp); simp [forumSet] at this h; omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hk
    have ha := hs a (by simp); have hb := hs b (by simp); simp [forumSet] at ha hb h; omega

/-- `forumSet` has order exactly `3`. -/
@[category API, AMS 5 11]
theorem forumSet_hasOrder : HasOrder forumSet 3 :=
  ⟨forumSet_isAddBasisOfOrderLE_three, fun k hk hA =>
    forumSet_not_isAddBasisOfOrderLE_two (hA.mono (by omega))⟩

@[category API, AMS 5 11]
theorem forumSet_isRestrictedBasisOfOrderLE_six : IsRestrictedBasisOfOrderLE forumSet 6 := by
  refine Filter.eventually_atTop.2 ⟨400, fun n hn => ?_⟩
  have hr := Nat.mod_lt n (show 10 > 0 by norm_num)
  interval_cases hm : n % 10
  · exact exists_finset_of_list [n] (by simp) (by simp [forumSet]; omega) (by simp) (by simp)
  · exact exists_finset_of_list [6, 13, 23, 33, 43, n - 118] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [6, 13, 23, n - 42] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [n] (by simp) (by simp [forumSet]; omega) (by simp) (by simp)
  · exact exists_finset_of_list [4, n - 4] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [6, 13, 23, 33, n - 75] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [6, n - 6] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [4, n - 4] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [6, 13, 23, 33, n - 75] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)
  · exact exists_finset_of_list [6, n - 6] (by simp; omega)
      (by simp [forumSet]; omega) (by simp) (by simp; omega)

/-- Residue bookkeeping for sums of distinct elements of `forumSet`: `x = [4 ∈ s]`,
`y = [6 ∈ s]`, and `k` counts (a lower bound for) the elements `≡ 3 (mod 10)`. -/
@[category API, AMS 5 11]
lemma forumSet_finset_invariant (s : Finset ℕ) (hs : (↑s : Set ℕ) ⊆ forumSet) :
    ∃ x y k : ℕ, x ≤ 1 ∧ y ≤ 1 ∧ (x = 1 ↔ 4 ∈ s) ∧ (y = 1 ↔ 6 ∈ s) ∧
      (∑ a ∈ s, a) % 10 = (4 * x + 6 * y + 3 * k) % 10 ∧ x + y + k ≤ s.card := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp⟩
  | insert a s has ih =>
    rw [Finset.coe_insert, Set.insert_subset_iff] at hs
    obtain ⟨x, y, k, hx, hy, hx4, hy6, hsum, hcard⟩ := ih hs.2
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has]
    simp only [Finset.mem_insert]
    rcases hs.1 with rfl | rfl | ⟨h0, -⟩ | ⟨h3, -⟩
    · have : x = 0 := by by_contra h; exact has (hx4.1 (by omega))
      exact ⟨1, y, k, le_rfl, hy, by simp, by simpa using hy6, by omega, by omega⟩
    · have : y = 0 := by by_contra h; exact has (hy6.1 (by omega))
      exact ⟨x, 1, k, hx, le_rfl, by simpa using hx4, by simp, by omega, by omega⟩
    · exact ⟨x, y, k, hx, hy, by rw [← hx4]; omega, by rw [← hy6]; omega, by omega, by omega⟩
    · exact ⟨x, y, k + 1, hx, hy, by rw [← hx4]; omega, by rw [← hy6]; omega, by omega,
        by omega⟩

/-- No integer `≡ 1 (mod 10)` is a sum of at most five distinct elements of `forumSet`. -/
@[category API, AMS 5 11]
theorem forumSet_not_isRestrictedBasisOfOrderLE_five :
    ¬ IsRestrictedBasisOfOrderLE forumSet 5 := by
  intro hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  obtain ⟨s, hs, hc, h⟩ := hN (10 * N + 1) (by omega)
  obtain ⟨x, y, k, hx, hy, -, -, hsum, hcard⟩ := forumSet_finset_invariant s hs
  rw [h] at hsum
  have hk : k ≤ 5 := by omega
  interval_cases x <;> interval_cases y <;> interval_cases k <;> omega

/-- `forumSet` has restricted order exactly `6`. -/
@[category API, AMS 5 11]
theorem forumSet_hasRestrictedOrder : HasRestrictedOrder forumSet 6 :=
  ⟨forumSet_isRestrictedBasisOfOrderLE_six, fun k hk hA =>
    forumSet_not_isRestrictedBasisOfOrderLE_five (hA.mono (by omega))⟩

@[category API, AMS 5 11]
lemma range_sum_facts (Q k : ℕ) :
    ((Multiset.range k).map (fun i => 10 * (Q + i) + 3)).sum % 10 = (3 * k) % 10 ∧
    ((Multiset.range k).map (fun i => 10 * (Q + i) + 3)).sum ≤ k * (10 * (Q + k) + 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.sum_cons]
    obtain ⟨h1, h2⟩ := ih
    constructor
    · omega
    · have : k * (10 * (Q + k) + 3) ≤ k * (10 * (Q + (k + 1)) + 3) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith

/-- For every finite `F`, `forumSet \ F` is still a basis (of order at most `10`). -/
@[category API, AMS 5 11]
theorem forumSet_sdiff_isAddBasisOfOrderLE (F : Finset ℕ) :
    IsAddBasisOfOrderLE (forumSet \ ↑F) 10 := by
  set Q := F.sup id + 1 with hQ
  have hF : ∀ m, Q ≤ m → m ∉ F := fun m hm hmF => by
    have := Finset.le_sup (f := id) hmF; simp at this; omega
  refine Filter.eventually_atTop.2 ⟨200 * Q + 2000, fun n hn => ?_⟩
  set k := (7 * n) % 10 with hk
  have hk9 : k < 10 := Nat.mod_lt _ (by norm_num)
  set S := ((Multiset.range k).map (fun i => 10 * (Q + i) + 3)).sum with hS
  obtain ⟨hS1, hS2⟩ := range_sum_facts Q k
  rw [← hS] at hS1 hS2
  have hS3 : S ≤ 9 * (10 * (Q + 9) + 3) :=
    hS2.trans (Nat.mul_le_mul (by omega) (by omega))
  refine ⟨(n - S) ::ₘ (Multiset.range k).map (fun i => 10 * (Q + i) + 3), ?_, ?_, ?_⟩
  · intro a ha
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)), hF _ (by omega)⟩
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
      exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)), hF _ (by omega)⟩
  · simp; omega
  · rw [Multiset.sum_cons, ← hS]; omega

/-- **Forum example** (verified): `{4, 6} ∪ {10q : q ≥ 1} ∪ {10q + 3 : q ≥ 1}` has order `3`,
restricted order `6`, and stays a basis after removing any finite set. -/
@[category test, AMS 5 11]
theorem erdos_338.variants.forum_example :
    HasOrder forumSet 3 ∧ HasRestrictedOrder forumSet 6 ∧
      ∀ F : Finset ℕ, IsAddBasis (forumSet \ ↑F) :=
  ⟨forumSet_hasOrder, forumSet_hasRestrictedOrder,
    fun F => ⟨10, forumSet_sdiff_isAddBasisOfOrderLE F⟩⟩

/-- The set of squares `{0, 1, 4, 9, …}`. -/
def squareSet : Set ℕ := {n | IsSquare n}

@[category API, AMS 5 11]
lemma squareSet_mod_eight {a : ℕ} (ha : a ∈ squareSet) :
    a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 4 := by
  obtain ⟨m, rfl⟩ := ha
  rw [Nat.mul_mod]
  have := Nat.mod_lt m (show 8 > 0 by norm_num)
  interval_cases m % 8 <;> simp

@[category API, AMS 5 11]
theorem squareSet_isAddBasisOfOrderLE_four : IsAddBasisOfOrderLE squareSet 4 := by
  refine Filter.Eventually.of_forall fun n => ?_
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨{a ^ 2, b ^ 2, c ^ 2, d ^ 2}, ?_, by simp, by simp [← h]; ring⟩
  intro x hx
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, sq _⟩

/-- No integer `≡ 7 (mod 8)` is a sum of at most three squares. -/
@[category API, AMS 5 11]
theorem squareSet_not_isAddBasisOfOrderLE_three : ¬ IsAddBasisOfOrderLE squareSet 3 := by
  intro hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  obtain ⟨s, hs, hc, h⟩ := hN (8 * N + 7) (by omega)
  have : Multiset.card s = 0 ∨ Multiset.card s = 1 ∨ Multiset.card s = 2 ∨
      Multiset.card s = 3 := by omega
  rcases this with hk | hk | hk | hk
  · rw [Multiset.card_eq_zero] at hk; subst hk; simp at h
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hk
    have := squareSet_mod_eight (hs a (by simp)); simp at h; omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hk
    have ha := squareSet_mod_eight (hs a (by simp))
    have hb := squareSet_mod_eight (hs b (by simp)); simp at h; omega
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.1 hk
    have ha := squareSet_mod_eight (hs a (by simp))
    have hb := squareSet_mod_eight (hs b (by simp))
    have hc := squareSet_mod_eight (hs c (by simp)); simp at h; omega

/-- The set of squares has order exactly `4`. -/
@[category research solved, AMS 5 11]
theorem erdos_338.variants.squares_order : HasOrder squareSet 4 :=
  ⟨squareSet_isAddBasisOfOrderLE_four, fun k hk hA =>
    squareSet_not_isAddBasisOfOrderLE_three (hA.mono (by omega))⟩

end Erdos338
