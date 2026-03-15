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
# Erdős Problem 494

*References:*
  - [erdosproblems.com/494](https://www.erdosproblems.com/494)
  - [SeSt58] Selfridge, J. L. and Straus, E., On the determination of numbers by their sums
      of a fixed order. Pacific Journal of Math. (1958), 847-856.
  - [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
      221-254.
  - [GFS62] Gordon, B. and Fraenkel, A. S. and Straus, E. G., On the determination of sets
      by the sets of sums of a certain order. Pacific J. Math. (1962), 187--196.
-/

open Filter

namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B




set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma sumMultiset_self (A : Finset ℂ ) :
    sumMultiset A A.card = {A.sum id} := by
  simp [sumMultiset, Finset.powersetCard_self]

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private noncomputable def counterexampleA (k : ℕ ) : Finset ℂ :=
  (Finset.range k).image fun n : ℕ => (n : ℂ)

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private noncomputable def counterexampleB (k : ℕ ) : Finset ℂ :=
  insert (((k - 1 : ℕ ) : ℂ ) - Complex.I)
    (insert (((k - 2 : ℕ ) : ℂ ) + Complex.I)
      ((Finset.range (k - 2)).image fun n : ℕ => (n : ℂ)))

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexampleA_card (k : ℕ ) :
    (counterexampleA k).card = k := by
  rw [counterexampleA, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Nat.cast_injective h

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexampleB_card (k : ℕ ) (hk : k > 2) :
    (counterexampleB k).card = k := by
  have h1 : (((k - 2 : ℕ ) : ℂ ) + Complex.I) ∉
      ((Finset.range (k - 2)).image fun n : ℕ => (n : ℂ)) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨x, hx, hEq⟩
    have him : (x : ℂ ).im = ((((k - 2 : ℕ ) : ℂ ) + Complex.I)).im := by
      simpa using congrArg Complex.im hEq
    norm_num at him
  have h2' : (((k - 1 : ℕ ) : ℂ ) - Complex.I) ≠ (((k - 2 : ℕ ) : ℂ ) + Complex.I) := by
    have him : ((((k - 1 : ℕ ) : ℂ ) - Complex.I).im) ≠
        ((((k - 2 : ℕ ) : ℂ ) + Complex.I).im) := by
      norm_num
    intro h
    exact him (by simpa using congrArg Complex.im h)
  have h2 : (((k - 1 : ℕ ) : ℂ ) - Complex.I) ∉
      insert (((k - 2 : ℕ ) : ℂ ) + Complex.I)
        ((Finset.range (k - 2)).image fun n : ℕ => (n : ℂ)) := by
    intro h
    rcases Finset.mem_insert.mp h with hEq | hMem
    · exact h2' hEq
    · rcases Finset.mem_image.mp hMem with ⟨x, hx, hEq⟩
      have him : (x : ℂ ).im = ((((k - 1 : ℕ ) : ℂ ) - Complex.I).im) := by
        simpa using congrArg Complex.im hEq
      norm_num at him
  rw [counterexampleB, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h1, Finset.card_image_of_injective]
  · have hk' : k - 2 + 1 + 1 = k := by
      omega
    simpa using hk'
  · intro a b h
    exact Nat.cast_injective h

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexample_range_sum (k : ℕ ) :
    (Finset.range k).sum (fun n : ℕ => (n : ℂ )) =
      (Finset.range (k - 2)).sum (fun n : ℕ => (n : ℂ )) +
        (((k - 2 : ℕ ) : ℂ ) + Complex.I) + (((k - 1 : ℕ ) : ℂ ) - Complex.I) := by
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero => simp
      | succ k =>
          simp [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]
          ring

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexampleA_sum (k : ℕ ) :
    (counterexampleA k).sum id = (Finset.range k).sum (fun n : ℕ => (n : ℂ )) := by
  rw [counterexampleA, Finset.sum_image]
  · rfl
  · intro a ha b hb h
    exact Nat.cast_injective h

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexampleB_sum (k : ℕ ) :
    (counterexampleB k).sum id =
      (((k - 1 : ℕ ) : ℂ ) - Complex.I) +
        ((((k - 2 : ℕ ) : ℂ ) + Complex.I) +
          (Finset.range (k - 2)).sum (fun n : ℕ => (n : ℂ ))) := by
  rw [counterexampleB, Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_image]
      · simp [add_assoc]
      · intro a ha b hb h
        exact Nat.cast_injective h
    · intro h
      rcases Finset.mem_image.mp h with ⟨x, hx, hEq⟩
      have him : (x : ℂ ).im = ((((k - 2 : ℕ ) : ℂ ) + Complex.I)).im := by
        simpa using congrArg Complex.im hEq
      norm_num at him
  · intro h
    rcases Finset.mem_insert.mp h with hEq | hMem
    · have him : ((((k - 1 : ℕ ) : ℂ ) - Complex.I).im) ≠
        ((((k - 2 : ℕ ) : ℂ ) + Complex.I).im) := by
        norm_num
      exact him (by simpa using congrArg Complex.im hEq)
    · rcases Finset.mem_image.mp hMem with ⟨x, hx, hEq⟩
      have him : (x : ℂ ).im = ((((k - 1 : ℕ ) : ℂ ) - Complex.I).im) := by
        simpa using congrArg Complex.im hEq
      norm_num at him

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexample_sums_match (k : ℕ ) :
    (counterexampleA k).sum id = (counterexampleB k).sum id := by
  rw [counterexampleA_sum, counterexampleB_sum, counterexample_range_sum]
  abel

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private lemma counterexample_ne (k : ℕ ) :
    counterexampleA k ≠ counterexampleB k := by
  intro hEq
  have hmem : (((k - 2 : ℕ ) : ℂ ) + Complex.I) ∈ counterexampleA k := by
    rw [hEq, counterexampleB]
    simp
  rw [counterexampleA] at hmem
  rcases Finset.mem_image.mp hmem with ⟨x, hx, hxEq⟩
  have him : (x : ℂ ).im = ((((k - 2 : ℕ ) : ℂ ) + Complex.I)).im := by
    simpa using congrArg Complex.im hxEq
  norm_num at him

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true when $k = 2$ and
$|A| \ne 2^l$ for $l \ge 0$.
They also gave counterexamples when $k = 2$ and $|A| = 2^l$.
-/

@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_2_card_not_pow_two :
    forall card : Nat, (forall l : Nat, card != 2 ^ l) -> Erdos494Unique 2 card := by
  sorry


section

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

private def natShiftEmbedding (m : Nat) : Nat ↪ Nat where
  toFun n := m + n
  inj' _ _ h := Nat.add_left_cancel h

private def natCastComplexEmbedding : Nat ↪ Complex where
  toFun n := (n : Complex)
  inj' _ _ h := Nat.cast_injective h

private def pairWithEmbedding (x : Nat) : Nat ↪ Finset Nat where
  toFun a := insert x {a}
  inj' a b h := by
    by_cases hax : a = x <;> by_cases hbx : b = x
    · simpa [hax, hbx]
    · have hbmem : b ∈ insert x ({a} : Finset Nat) := by
        simpa [h] using (show b ∈ insert x ({b} : Finset Nat) by simp)
      have : False := by simpa [hax, hbx] using hbmem
      exact False.elim this
    · have hamem : a ∈ insert x ({b} : Finset Nat) := by
        simpa [h] using (show a ∈ insert x ({a} : Finset Nat) by simp)
      have : False := by simpa [hax, hbx] using hamem
      exact False.elim this
    · have hxna : x ∉ ({a} : Finset Nat) := by
        intro hx'
        have hxa : x = a := by simpa using hx'
        exact hax hxa.symm
      have hxnb : x ∉ ({b} : Finset Nat) := by
        intro hx'
        have hxb : x = b := by simpa using hx'
        exact hbx hxb.symm
      have hs : ({a} : Finset Nat) = {b} := by
        calc
          ({a} : Finset Nat) = (insert x ({a} : Finset Nat)).erase x := by
            rw [Finset.erase_insert hxna]
          _ = (insert x ({b} : Finset Nat)).erase x := by
            simpa using congrArg (fun s : Finset Nat => s.erase x) h
          _ = {b} := by
            rw [Finset.erase_insert hxnb]
      exact Finset.singleton_injective hs

private def sumMultisetNat (A : Finset Nat) (k : Nat) : Multiset Nat :=
  (A.powersetCard k).val.map fun s => s.sum id

private lemma val_union_of_disjoint {alpha : Type} [DecidableEq alpha] {A B : Finset alpha}
    (h : Disjoint A B) :
    (A ∪ B).val = A.val + B.val := by
  rw [Finset.union_val_nd]
  simpa [Multiset.dedup_eq_self.2 A.nodup] using
    (Multiset.Disjoint.ndunion_eq (s := A.val) (t := B.val) (Finset.disjoint_val.2 h))

private lemma image_insert_powersetCard_one (A : Finset Nat) (x : Nat) :
    (A.powersetCard 1).image (insert x) = A.map (pairWithEmbedding x) := by
  rw [Finset.powersetCard_one]
  ext s
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    rcases Finset.mem_map.mp ht with ⟨a, ha, rfl⟩
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨a, ha, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨{a}, ?_, rfl⟩
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩

private lemma sum_map_shift (m : Nat) (s : Finset Nat) :
    (s.map (natShiftEmbedding m)).sum id = s.sum id + s.card * m := by
  rw [Finset.sum_map]
  simp [natShiftEmbedding]
  rw [Finset.sum_add_distrib]
  simp [Nat.mul_comm, Nat.add_comm]

private lemma sumMultisetNat_map_shift (A : Finset Nat) (m : Nat) :
    sumMultisetNat (A.map (natShiftEmbedding m)) 2 =
      Multiset.map (fun n => n + 2 * m) (sumMultisetNat A 2) := by
  rw [sumMultisetNat, sumMultisetNat, Finset.powersetCard_map, Finset.map_val]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro s hs
  have hs_card : s.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_val.mp hs)).2
  have hmap : ((fun s => s.sum id) ∘ ⇑(Finset.mapEmbedding (natShiftEmbedding m)).toEmbedding) s =
      (s.map (natShiftEmbedding m)).sum id := rfl
  rw [hmap]
  simpa [hs_card, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (sum_map_shift m s)

private lemma sumMultisetNat_insert {A : Finset Nat} {x : Nat} (hx : x ∉ A) :
    sumMultisetNat (insert x A) 2 = sumMultisetNat A 2 + A.val.map (fun a => x + a) := by
  rw [sumMultisetNat, Finset.powersetCard_succ_insert hx 1]
  have hdisj : Disjoint (A.powersetCard 2) ((A.powersetCard 1).image (insert x)) := by
    rw [Finset.disjoint_left]
    intro s hsA hsx
    have hx_mem : x ∈ s := by
      rcases Finset.mem_image.mp hsx with ⟨t, ht, rfl⟩
      simp
    exact hx ((Finset.mem_powersetCard.mp hsA).1 hx_mem)
  have hval : ((A.powersetCard 2) ∪ ((A.powersetCard 1).image (insert x))).val =
      (A.powersetCard 2).val + ((A.powersetCard 1).image (insert x)).val := by
    simpa using (val_union_of_disjoint hdisj)
  rw [hval, Multiset.map_add]
  rw [sumMultisetNat, image_insert_powersetCard_one, Finset.map_val, Multiset.map_map]
  refine congrArg (sumMultisetNat A 2 + ·) ?_
  refine Multiset.map_congr rfl ?_
  intro a ha
  have hxa : x ≠ a := by
    intro hxa
    exact hx (by simpa [hxa] using ha)
  show (insert x ({a} : Finset Nat)).sum id = x + a
  simp [hxa]

private def crossSums (A B : Finset Nat) : Multiset Nat :=
  B.val.bind fun b => A.val.map fun a => b + a

private lemma crossSums_insert (A B : Finset Nat) {x : Nat} (hx : x ∉ B) :
    crossSums A (insert x B) = A.val.map (fun a => x + a) + crossSums A B := by
  unfold crossSums
  rw [Finset.insert_val_of_notMem hx, Multiset.cons_bind]

private lemma sumMultisetNat_union (A B : Finset Nat) (h : Disjoint A B) :
    sumMultisetNat (A ∪ B) 2 = sumMultisetNat A 2 + sumMultisetNat B 2 + crossSums A B := by
  revert A
  induction B using Finset.induction_on with
  | empty =>
      intro A h
      simp [crossSums, sumMultisetNat]
  | @insert x B hx ih =>
      intro A h
      have hxA : x ∉ A := (Finset.disjoint_insert_right.mp h).1
      have hAB : Disjoint A B := (Finset.disjoint_insert_right.mp h).2
      have hxUnion : x ∉ A ∪ B := by simp [hxA, hx]
      have hunion : A ∪ insert x B = insert x (A ∪ B) := by
        ext y
        simp [or_comm, or_left_comm, or_assoc]
      calc
        sumMultisetNat (A ∪ insert x B) 2
            = sumMultisetNat (insert x (A ∪ B)) 2 := by rw [hunion]
        _ = sumMultisetNat (A ∪ B) 2 + (A ∪ B).val.map (fun a => x + a) := by
            rw [sumMultisetNat_insert hxUnion]
        _ = sumMultisetNat A 2 + sumMultisetNat B 2 + crossSums A B +
              (A.val.map (fun a => x + a) + B.val.map (fun b => x + b)) := by
            rw [ih A hAB, val_union_of_disjoint hAB, Multiset.map_add]
        _ = sumMultisetNat A 2 + sumMultisetNat (insert x B) 2 + crossSums A (insert x B) := by
            rw [sumMultisetNat_insert (A := B) (x := x) hx,
              crossSums_insert (A := A) (B := B) (x := x) hx]
            simpa [add_assoc, add_left_comm, add_comm]

private lemma crossSums_comm (A B : Finset Nat) : crossSums A B = crossSums B A := by
  unfold crossSums
  simpa [Nat.add_comm] using (Multiset.bind_map_comm B.val A.val (f := fun b a => b + a))

private lemma crossSums_map_shift (A B : Finset Nat) (m : Nat) :
    crossSums A (B.map (natShiftEmbedding m)) =
      Multiset.map (fun n => n + m) (crossSums A B) := by
  unfold crossSums
  rw [Finset.map_val, Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr ?_
  intro b hb
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro a ha
  simp [natShiftEmbedding, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

mutual
  private def powTwoA : Nat → Finset Nat
    | 0 => {0}
    | l + 1 => powTwoA l ∪ (powTwoB l).map (natShiftEmbedding (2 ^ (l + 1)))

  private def powTwoB : Nat → Finset Nat
    | 0 => {1}
    | l + 1 => powTwoB l ∪ (powTwoA l).map (natShiftEmbedding (2 ^ (l + 1)))
end

private lemma powTwo_range :
    ∀ l, powTwoA l ⊆ Finset.range (2 ^ (l + 1)) ∧ powTwoB l ⊆ Finset.range (2 ^ (l + 1)) := by
  intro l
  induction l with
  | zero =>
      constructor <;> simp [powTwoA, powTwoB]
  | succ l ih =>
      rcases ih with ⟨ihA, ihB⟩
      constructor
      · intro x hx
        rw [powTwoA, Finset.mem_union, Finset.mem_map] at hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact Finset.mem_range.mpr (by
            have hxlt : x < 2 ^ (l + 1) := Finset.mem_range.mp (ihA hx)
            omega)
        · exact Finset.mem_range.mpr (by
            have hylt : y < 2 ^ (l + 1) := Finset.mem_range.mp (ihB hy)
            have hylt' : 2 ^ (l + 1) + y < 2 ^ (l + 1) + 2 ^ (l + 1) :=
              Nat.add_lt_add_left hylt (2 ^ (l + 1))
            have hpow : 2 ^ (l + 2) = 2 ^ (l + 1) + 2 ^ (l + 1) := by
              calc
                2 ^ (l + 2) = 2 ^ ((l + 1) + 1) := by
                  rw [show l + 2 = (l + 1) + 1 by omega]
                _ = 2 ^ (l + 1) * 2 := by rw [pow_succ]
                _ = 2 ^ (l + 1) + 2 ^ (l + 1) := by rw [Nat.mul_comm, two_mul]
            rw [hpow]
            simpa [natShiftEmbedding] using hylt')
      · intro x hx
        rw [powTwoB, Finset.mem_union, Finset.mem_map] at hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact Finset.mem_range.mpr (by
            have hxlt : x < 2 ^ (l + 1) := Finset.mem_range.mp (ihB hx)
            omega)
        · exact Finset.mem_range.mpr (by
            have hylt : y < 2 ^ (l + 1) := Finset.mem_range.mp (ihA hy)
            have hylt' : 2 ^ (l + 1) + y < 2 ^ (l + 1) + 2 ^ (l + 1) :=
              Nat.add_lt_add_left hylt (2 ^ (l + 1))
            have hpow : 2 ^ (l + 2) = 2 ^ (l + 1) + 2 ^ (l + 1) := by
              calc
                2 ^ (l + 2) = 2 ^ ((l + 1) + 1) := by
                  rw [show l + 2 = (l + 1) + 1 by omega]
                _ = 2 ^ (l + 1) * 2 := by rw [pow_succ]
                _ = 2 ^ (l + 1) + 2 ^ (l + 1) := by rw [Nat.mul_comm, two_mul]
            rw [hpow]
            simpa [natShiftEmbedding] using hylt')

private lemma powTwoA_range (l : Nat) : powTwoA l ⊆ Finset.range (2 ^ (l + 1)) :=
  (powTwo_range l).1

private lemma powTwoB_range (l : Nat) : powTwoB l ⊆ Finset.range (2 ^ (l + 1)) :=
  (powTwo_range l).2

private lemma powTwo_disjointA (l : Nat) :
    Disjoint (powTwoA l) ((powTwoB l).map (natShiftEmbedding (2 ^ (l + 1)))) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  rcases Finset.mem_map.mp hxB with ⟨y, hyB, rfl⟩
  have hxlt : (natShiftEmbedding (2 ^ (l + 1))) y < 2 ^ (l + 1) :=
    Finset.mem_range.mp (powTwoA_range l hxA)
  have : 2 ^ (l + 1) + y < 2 ^ (l + 1) := by simpa [natShiftEmbedding] using hxlt
  omega

private lemma powTwo_disjointB (l : Nat) :
    Disjoint (powTwoB l) ((powTwoA l).map (natShiftEmbedding (2 ^ (l + 1)))) := by
  rw [Finset.disjoint_left]
  intro x hxB hxA
  rcases Finset.mem_map.mp hxA with ⟨y, hyA, rfl⟩
  have hxlt : (natShiftEmbedding (2 ^ (l + 1))) y < 2 ^ (l + 1) :=
    Finset.mem_range.mp (powTwoB_range l hxB)
  have : 2 ^ (l + 1) + y < 2 ^ (l + 1) := by simpa [natShiftEmbedding] using hxlt
  omega

private lemma powTwo_card :
    ∀ l, (powTwoA l).card = 2 ^ l ∧ (powTwoB l).card = 2 ^ l := by
  intro l
  induction l with
  | zero =>
      constructor <;> simp [powTwoA, powTwoB]
  | succ l ih =>
      rcases ih with ⟨ihA, ihB⟩
      constructor
      · rw [powTwoA, Finset.card_union_of_disjoint, Finset.card_map, ihA, ihB]
        · omega
        · exact powTwo_disjointA l
      · rw [powTwoB, Finset.card_union_of_disjoint, Finset.card_map, ihA, ihB]
        · omega
        · exact powTwo_disjointB l

private lemma powTwoA_card (l : Nat) : (powTwoA l).card = 2 ^ l := (powTwo_card l).1

private lemma powTwoB_card (l : Nat) : (powTwoB l).card = 2 ^ l := (powTwo_card l).2

private lemma zero_mem_powTwoA : ∀ l, 0 ∈ powTwoA l := by
  intro l
  induction l with
  | zero => simp [powTwoA]
  | succ l ih =>
      rw [powTwoA, Finset.mem_union]
      exact Or.inl ih

private lemma zero_not_mem_powTwoB : ∀ l, 0 ∉ powTwoB l := by
  intro l
  induction l with
  | zero => simp [powTwoB]
  | succ l ih =>
      rw [powTwoB, Finset.mem_union]
      intro h
      rcases h with h | h
      · exact ih h
      · rcases Finset.mem_map.mp h with ⟨y, hy, hyEq⟩
        have hpow : 0 < 2 ^ (l + 1) := by
          exact pow_pos (by decide) _
        have : 2 ^ (l + 1) + y = 0 := by simpa [natShiftEmbedding] using hyEq
        omega

private lemma sumMultiset_cast (A : Finset Nat) :
    sumMultiset (A.map natCastComplexEmbedding) 2 =
      Multiset.map natCastComplexEmbedding (sumMultisetNat A 2) := by
  rw [sumMultiset, sumMultisetNat, Finset.powersetCard_map, Finset.map_val]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro s hs
  calc
    (s.map natCastComplexEmbedding).sum id = s.sum (fun x => (x : Complex)) := by
      simpa [natCastComplexEmbedding] using (Finset.sum_map s natCastComplexEmbedding (fun z : Complex => z))
    _ = natCastComplexEmbedding (s.sum id) := by
      simp [natCastComplexEmbedding, Nat.cast_sum]

private lemma powTwo_pair_sums : ∀ l, sumMultisetNat (powTwoA l) 2 = sumMultisetNat (powTwoB l) 2 := by
  intro l
  induction l with
  | zero =>
      native_decide
  | succ l ih =>
      let M := 2 ^ (l + 1)
      calc
        sumMultisetNat (powTwoA (l + 1)) 2
            = sumMultisetNat (powTwoA l) 2 +
                sumMultisetNat ((powTwoB l).map (natShiftEmbedding M)) 2 +
                crossSums (powTwoA l) ((powTwoB l).map (natShiftEmbedding M)) := by
              simpa [powTwoA, M] using
                (sumMultisetNat_union (powTwoA l)
                  ((powTwoB l).map (natShiftEmbedding M))
                  (powTwo_disjointA l))
        _ = sumMultisetNat (powTwoB l) 2 +
                sumMultisetNat ((powTwoA l).map (natShiftEmbedding M)) 2 +
                crossSums (powTwoB l) ((powTwoA l).map (natShiftEmbedding M)) := by
              rw [sumMultisetNat_map_shift, sumMultisetNat_map_shift,
                crossSums_map_shift, crossSums_map_shift]
              have hcross :
                  Multiset.map (fun n => n + M) (crossSums (powTwoA l) (powTwoB l)) =
                    Multiset.map (fun n => n + M) (crossSums (powTwoB l) (powTwoA l)) := by
                exact congrArg (Multiset.map (fun n => n + M)) (crossSums_comm (powTwoA l) (powTwoB l))
              rw [ih, hcross]
        _ = sumMultisetNat (powTwoB (l + 1)) 2 := by
              simpa [powTwoB, M] using
                (sumMultisetNat_union (powTwoB l)
                  ((powTwoA l).map (natShiftEmbedding M))
                  (powTwo_disjointB l)).symm

@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_2_card_pow_two :
    ∀ card : Nat, (∃ l : Nat, card = 2 ^ l) → ¬Erdos494Unique 2 card := by
  intro card hpow huniq
  rcases hpow with ⟨l, rfl⟩
  let A : Finset Complex := (powTwoA l).map natCastComplexEmbedding
  let B : Finset Complex := (powTwoB l).map natCastComplexEmbedding
  have hAcard : A.card = 2 ^ l := by
    simpa [A] using powTwoA_card l
  have hBcard : B.card = 2 ^ l := by
    simpa [B] using powTwoB_card l
  have hsm : sumMultiset A 2 = sumMultiset B 2 := by
    calc
      sumMultiset A 2 = Multiset.map natCastComplexEmbedding (sumMultisetNat (powTwoA l) 2) := by
        simpa [A] using sumMultiset_cast (powTwoA l)
      _ = Multiset.map natCastComplexEmbedding (sumMultisetNat (powTwoB l) 2) := by
        exact congrArg (Multiset.map natCastComplexEmbedding) (powTwo_pair_sums l)
      _ = sumMultiset B 2 := by
        simpa [B] using (sumMultiset_cast (powTwoB l)).symm
  have hEq : A = B := huniq A B hAcard hBcard hsm
  have h0A : (0 : Complex) ∈ A := by
    apply Finset.mem_map.mpr
    refine Exists.intro 0 ?_
    exact And.intro (zero_mem_powTwoA l) (by simp [natCastComplexEmbedding])
  have h0B : (0 : Complex) ∉ B := by
    intro h0
    rcases Finset.mem_map.mp h0 with ⟨n, hn, hn0⟩
    have : n = 0 := Nat.cast_injective (by simpa using hn0)
    subst this
    exact zero_not_mem_powTwoB l hn
  exact h0B (hEq ▸ h0A)

end

/--
Selfridge and Straus [SeSt58] also showed that the conjecture is true when
1) $k = 3$ and $|A| > 6$ or
2) $k = 4$ and $|A| > 12$.
More generally, they proved that $A$ is determined by $A_k$ (and $|A|$) if $|A|$ is divisible by
a prime greater than $k$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_3_card_gt_6 :
    ∀ card > 6, Erdos494Unique 3 card := by
  sorry

@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_4_card_gt_12 :
    ∀ card > 12, Erdos494Unique 4 card := by
  sorry

@[category research solved, AMS 5]
theorem erdos_494.variants.card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card := by
  sorry

/--
Kruyt noted that the conjecture fails when $|A| = k$, by rotating $A$ around an appropriate point.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_card :
    ∀ k > 2, ¬Erdos494Unique k k := by
  intro k hk huniq
  have hsm : sumMultiset (counterexampleA k) k = sumMultiset (counterexampleB k) k := by
    calc
      sumMultiset (counterexampleA k) k = sumMultiset (counterexampleA k) (counterexampleA k).card := by
        simp [counterexampleA_card]
      _ = {(counterexampleA k).sum id} := sumMultiset_self (counterexampleA k)
      _ = {(counterexampleB k).sum id} := by rw [counterexample_sums_match]
      _ = sumMultiset (counterexampleB k) (counterexampleB k).card :=
        (sumMultiset_self (counterexampleB k)).symm
      _ = sumMultiset (counterexampleB k) k := by
        simp [counterexampleB_card, hk]
  exact counterexample_ne k
    (huniq (counterexampleA k) (counterexampleB k) (counterexampleA_card k)
      (counterexampleB_card k hk) hsm)


section

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

private noncomputable def negImage (A : Finset ℂ) : Finset ℂ :=
  A.image fun z => -z

private lemma negImage_card (A : Finset ℂ) : (negImage A).card = A.card := by
  rw [negImage, Finset.card_image_of_injective]
  intro a b h
  simpa using neg_injective h

private lemma sum_negImage (A : Finset ℂ) :
    (negImage A).sum id = -A.sum id := by
  rw [negImage, Finset.sum_image]
  · simpa using Finset.sum_neg_distrib (fun x : ℂ => x) (s := A)
  · intro a _ b _ h
    simpa using neg_injective h

private lemma mem_powersetCard_negImage {A s : Finset ℂ} {k : ℕ}
    (hs : s ∈ A.powersetCard k) :
    s.image (fun z => -z) ∈ (negImage A).powersetCard k := by
  rw [Finset.mem_powersetCard] at hs ⊢
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hs.1 hy, by simp⟩
  · rw [Finset.card_image_of_injective]
    . exact hs.2
    . intro a b h
      simpa using neg_injective h

private lemma powersetCard_negImage (A : Finset ℂ) (k : ℕ) :
    (negImage A).powersetCard k = (A.powersetCard k).image (fun s => s.image fun z => -z) := by
  ext s
  constructor
  · intro hs
    have hs' : s.image (fun z => -z) ∈ A.powersetCard k := by
      rw [Finset.mem_powersetCard] at hs ⊢
      refine ⟨?_, ?_⟩
      . intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rcases Finset.mem_image.mp (hs.1 hy) with ⟨z, hz, hzEq⟩
        have hz' : z = -y := by
          simpa using congrArg Neg.neg hzEq
        simpa [hz'] using hz
      . rw [Finset.card_image_of_injective]
        . exact hs.2
        . intro a b h
          simpa using neg_injective h
    refine Finset.mem_image.mpr ?_
    refine ⟨s.image (fun z => -z), hs', ?_⟩
    ext x
    simp
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    exact mem_powersetCard_negImage ht

private lemma subset_neg_injective : Function.Injective (fun s : Finset ℂ => s.image fun z => -z) := by
  intro s t hst
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hx' : -x ∈ s.image (fun z => -z) := by
      exact Finset.mem_image.mpr ⟨x, hx, by simp⟩
    have hx'' : -x ∈ t.image (fun z => -z) := by
      simpa [hst] using hx'
    rcases Finset.mem_image.mp hx'' with ⟨y, hy, hyEq⟩
    have hy' : y = x := by
      simpa using congrArg Neg.neg hyEq
    simpa [hy'] using hy
  · intro hx
    have hx' : -x ∈ t.image (fun z => -z) := by
      exact Finset.mem_image.mpr ⟨x, hx, by simp⟩
    have hx'' : -x ∈ s.image (fun z => -z) := by
      simpa [hst] using hx'
    rcases Finset.mem_image.mp hx'' with ⟨y, hy, hyEq⟩
    have hy' : y = x := by
      simpa using congrArg Neg.neg hyEq
    simpa [hy'] using hy

private lemma sumMultiset_negImage_formula (A : Finset ℂ) (k : ℕ) :
    sumMultiset (negImage A) k = ((A.powersetCard k).val.map fun s => -s.sum id) := by
  rw [sumMultiset, powersetCard_negImage, Finset.image_val]
  rw [Multiset.dedup_eq_self.mpr]
  · rw [Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro s hs
    simpa [negImage] using sum_negImage s
  · exact Multiset.Nodup.map subset_neg_injective (Finset.nodup _)

private lemma compl_mem_powersetCard {A s : Finset ℂ} {k : ℕ}
    (hA : A.card = 2 * k) (hs : s ∈ A.powersetCard k) :
    A \ s ∈ A.powersetCard k := by
  rw [Finset.mem_powersetCard] at hs ⊢
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset hs.1, hA, hs.2]
  omega

private lemma sum_compl_eq_neg {A s : Finset ℂ} (hs : s ⊆ A) (hSum : A.sum id = 0) :
    (A \ s).sum id = -s.sum id := by
  rw [Finset.sum_sdiff_eq_sub hs, hSum]
  abel

private lemma powersetCard_compl (A : Finset ℂ) (k : ℕ) (hA : A.card = 2 * k) :
    A.powersetCard k = (A.powersetCard k).image (fun s => A \ s) := by
  ext s
  constructor
  · intro hs
    refine Finset.mem_image.mpr ?_
    exact ⟨A \ s, compl_mem_powersetCard hA hs, by
      simp [Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp hs).1]⟩
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    exact compl_mem_powersetCard hA ht

private lemma sumMultiset_compl_formula (A : Finset ℂ) (k : ℕ) (hA : A.card = 2 * k) :
    sumMultiset A k = ((A.powersetCard k).val.map fun s => (A \ s).sum id) := by
  unfold sumMultiset
  conv_lhs => rw [powersetCard_compl A k hA, Finset.image_val]
  rw [Multiset.dedup_eq_self.mpr]
  · simp [Function.comp]
  · rw [Multiset.nodup_map_iff_inj_on (Finset.nodup _)]
    intro s hs t ht hst
    have hsA : s ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_val.mp hs)).1
    have htA : t ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_val.mp ht)).1
    calc
      s = A \ (A \ s) := by simpa using (Finset.sdiff_sdiff_eq_self hsA).symm
      _ = A \ (A \ t) := by rw [hst]
      _ = t := by simpa using Finset.sdiff_sdiff_eq_self htA

private lemma sumMultiset_eq_negImage (A : Finset ℂ) (k : ℕ)
    (hA : A.card = 2 * k) (hSum : A.sum id = 0) :
    sumMultiset A k = sumMultiset (negImage A) k := by
  rw [sumMultiset_compl_formula A k hA, sumMultiset_negImage_formula]
  refine Multiset.map_congr rfl ?_
  intro s hs
  have hsA : s ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_val.mp hs)).1
  exact sum_compl_eq_neg hsA hSum

private noncomputable def witnessC : Finset ℂ := {1, 2, 3, -6}

private noncomputable def witnessD (k : ℕ) : Finset ℂ :=
  (Finset.range (k - 2)).image fun n : ℕ => ((10 + n : ℕ) : ℂ)

private noncomputable def witnessA (k : ℕ) : Finset ℂ :=
  witnessC ∪ (witnessD k ∪ negImage (witnessD k))

private lemma mem_witnessD {k : ℕ} {x : ℂ} :
    x ∈ witnessD k ↔ ∃ n, n < k - 2 /\ x = ((10 + n : ℕ) : ℂ) := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    exact ⟨n, Finset.mem_range.mp hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩

private lemma mem_negImage_witnessD {k : ℕ} {x : ℂ} :
    x ∈ negImage (witnessD k) ↔ ∃ n, n < k - 2 /\ x = -((10 + n : ℕ) : ℂ) := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases mem_witnessD.mp hy with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact Finset.mem_image.mpr
      ⟨((10 + n : ℕ) : ℂ), mem_witnessD.mpr ⟨n, hn, rfl⟩, by simp⟩

private lemma nat_lt_ten_not_mem_witnessD (k m : ℕ) (hm : m < 10) :
    ((m : ℕ) : ℂ) ∉ witnessD k := by
  intro h
  rcases mem_witnessD.mp h with ⟨n, hn, hEq⟩
  have hEqR : (10 + n : Real) = m := by
    exact_mod_cast hEq.symm
  have hmR : (m : Real) < 10 := by
    exact_mod_cast hm
  have hnR : (0 : Real) <= n := by
    exact_mod_cast (Nat.zero_le n)
  nlinarith

private lemma neg_nat_not_mem_witnessD (k m : ℕ) :
    (-((m : ℕ) : ℂ)) ∉ witnessD k := by
  intro h
  rcases mem_witnessD.mp h with ⟨n, hn, hEq⟩
  have hEqR : (10 + n : Real) = -(m : Real) := by
    exact_mod_cast hEq.symm
  have hmR : (0 : Real) <= m := by
    exact_mod_cast (Nat.zero_le m)
  have hnR : (0 : Real) <= n := by
    exact_mod_cast (Nat.zero_le n)
  nlinarith

private lemma nat_not_mem_negImage_witnessD (k m : ℕ) :
    ((m : ℕ) : ℂ) ∉ negImage (witnessD k) := by
  intro h
  rcases mem_negImage_witnessD.mp h with ⟨n, hn, hEq⟩
  have hre : (((m : ℕ) : ℂ).re) = ((-((10 + n : ℕ) : ℂ)).re) := by
    simpa using congrArg Complex.re hEq
  norm_num at hre
  have hmR : (0 : Real) <= m := by
    exact_mod_cast (Nat.zero_le m)
  have hnR : (0 : Real) <= n := by
    exact_mod_cast (Nat.zero_le n)
  nlinarith

private lemma neg_nat_lt_ten_not_mem_negImage_witnessD (k m : ℕ) (hm : m < 10) :
    (-((m : ℕ) : ℂ)) ∉ negImage (witnessD k) := by
  intro h
  rcases mem_negImage_witnessD.mp h with ⟨n, hn, hEq⟩
  have hre : ((-((m : ℕ) : ℂ)).re) = ((-((10 + n : ℕ) : ℂ)).re) := by
    simpa using congrArg Complex.re hEq
  norm_num at hre
  have hmR : (m : Real) < 10 := by
    exact_mod_cast hm
  have hnR : (0 : Real) <= n := by
    exact_mod_cast (Nat.zero_le n)
  nlinarith

private lemma witnessC_disjoint_witnessD (k : ℕ) : Disjoint witnessC (witnessD k) := by
  rw [Finset.disjoint_left]
  intro x hxC hxD
  simp [witnessC] at hxC
  rcases hxC with rfl | rfl | rfl | rfl
  · exact (nat_lt_ten_not_mem_witnessD k 1 (by omega)) (by simpa using hxD)
  · exact (nat_lt_ten_not_mem_witnessD k 2 (by omega)) (by simpa using hxD)
  · exact (nat_lt_ten_not_mem_witnessD k 3 (by omega)) (by simpa using hxD)
  · exact (neg_nat_not_mem_witnessD k 6) (by simpa using hxD)

private lemma witnessC_disjoint_negImage_witnessD (k : ℕ) :
    Disjoint witnessC (negImage (witnessD k)) := by
  rw [Finset.disjoint_left]
  intro x hxC hxD
  simp [witnessC] at hxC
  rcases hxC with rfl | rfl | rfl | rfl
  · exact (nat_not_mem_negImage_witnessD k 1) (by simpa using hxD)
  · exact (nat_not_mem_negImage_witnessD k 2) (by simpa using hxD)
  · exact (nat_not_mem_negImage_witnessD k 3) (by simpa using hxD)
  · exact (neg_nat_lt_ten_not_mem_negImage_witnessD k 6 (by omega)) (by simpa using hxD)

private lemma witnessD_disjoint_negImage_witnessD (k : ℕ) :
    Disjoint (witnessD k) (negImage (witnessD k)) := by
  rw [Finset.disjoint_left]
  intro x hxD hxNeg
  rcases mem_witnessD.mp hxD with ⟨n, hn, rfl⟩
  exact (nat_not_mem_negImage_witnessD k (10 + n)) (by simpa using hxNeg)

private lemma witnessC_card : witnessC.card = 4 := by
  norm_num [witnessC]

private lemma witnessD_card (k : ℕ) : (witnessD k).card = k - 2 := by
  rw [witnessD, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Nat.add_left_cancel (Nat.cast_injective h)

private lemma witnessA_card (k : ℕ) (hk : k > 2) : (witnessA k).card = 2 * k := by
  rw [witnessA, Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint]
    . rw [witnessC_card, negImage_card, witnessD_card]
      omega
    . exact witnessD_disjoint_negImage_witnessD k
  · exact (Finset.disjoint_union_right).2
      ⟨witnessC_disjoint_witnessD k, witnessC_disjoint_negImage_witnessD k⟩

private lemma witnessC_sum : witnessC.sum id = 0 := by
  norm_num [witnessC]

private lemma witnessA_sum (k : ℕ) : (witnessA k).sum id = 0 := by
  rw [witnessA, Finset.sum_union]
  · rw [Finset.sum_union]
    . rw [witnessC_sum, sum_negImage]
      abel
    . exact witnessD_disjoint_negImage_witnessD k
  · exact (Finset.disjoint_union_right).2
      ⟨witnessC_disjoint_witnessD k, witnessC_disjoint_negImage_witnessD k⟩

private lemma one_mem_witnessA (k : ℕ) : (1 : ℂ) ∈ witnessA k := by
  simp [witnessA, witnessC]

private lemma neg_one_not_mem_witnessA (k : ℕ) : (-1 : ℂ) ∉ witnessA k := by
  intro h
  rw [witnessA, Finset.mem_union, Finset.mem_union] at h
  rcases h with hC | hD | hNeg
  · norm_num [witnessC] at hC
  · exact (neg_nat_not_mem_witnessD k 1) (by simpa using hD)
  · exact (neg_nat_lt_ten_not_mem_negImage_witnessD k 1 (by omega)) (by simpa using hNeg)

private lemma witnessA_ne_negImage (k : ℕ) : witnessA k ≠  negImage (witnessA k) := by
  intro hEq
  have hmem : (1 : ℂ) ∈ witnessA k := one_mem_witnessA k
  rw [hEq] at hmem
  rcases Finset.mem_image.mp hmem with ⟨x, hx, hxEq⟩
  have hx' : x = (-1 : ℂ) := by
    have := congrArg Neg.neg hxEq
    simpa using this
  exact neg_one_not_mem_witnessA k (hx' ▸ hx)

end

/--
Similarly, Tao noted that the conjecture fails when $|A| = 2k$, by taking $A$ to be a set of
the total sum 0 and considering $-A$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.card_eq_2k :
    ∀ k > 2, ¬Erdos494Unique k (2 * k) := by

  intro k hk huniq
  let A := witnessA k
  let B := negImage A
  have hAcard : A.card = 2 * k := by
    simpa [A] using witnessA_card k hk
  have hBcard : B.card = 2 * k := by
    simpa [B, hAcard] using negImage_card A
  have hAsum : A.sum id = 0 := by
    simpa [A] using witnessA_sum k
  have hsm : sumMultiset A k = sumMultiset B k := by
    simpa [B] using sumMultiset_eq_negImage A k hAcard hAsum
  have hEq : A = B := huniq A B hAcard hBcard hsm
  exact witnessA_ne_negImage k (by simpa [A, B] using hEq)

/--
Gordon, Fraenkel, and Straus [GRS62] proved that the claim is true for all $k > 2$ when
$|A|$ is sufficiently large.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.gordon_fraenkel_straus :
    ∀ k > 2, ∀ᶠ card in atTop, Erdos494Unique k card := by
  sorry

/--
A version in [Er61] by Erd?s is product instead of sum, which is false.
A simple counterexample is given by $k = 3$ with
$A = \{0, 1, 2\}$ and $B = \{0, 1, 3\}$.
-/
noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.prod id))

@[category research solved, AMS 5]
theorem erdos_494.variants.product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧
      A ≠ B := by
  use {0, 1, 2}, {0, 1, 3}
  simp [prodMultiset]
  simp [Finset.ext_iff]
  simp [Multiset.map] at *
  erw [Quot.liftOn_mk, Quot.liftOn_mk]
  norm_num
  exact ⟨3, by norm_num⟩

end Erdos494
