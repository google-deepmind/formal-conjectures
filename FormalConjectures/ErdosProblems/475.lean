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
# Erdős Problem 475

*Reference:* [erdosproblems.com/475](https://www.erdosproblems.com/475)
-/

@[expose] public section

namespace Erdos475

section General

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The nonempty partial sums $s_1,\ldots,s_t$. -/
def prefixSums (l : List G) : List G :=
  List.ofFn (fun i : Fin l.length => (l.take (i.val + 1)).sum)

/-- Every element occurs once, the element set is A, and the prefix sums differ. -/
def ValidOrdering (A : Finset G) (l : List G) : Prop :=
  l.Nodup ∧ l.toFinset = A ∧ (prefixSums l).Nodup

def HasValidOrdering (A : Finset G) : Prop := ∃ l : List G, ValidOrdering A l

omit [DecidableEq G] in
/-- The nonempty partial sums are distinct exactly when their indexing function is injective. -/
@[category API, AMS 5 11]
theorem prefixSums_nodup_iff (l : List G) :
    (prefixSums l).Nodup ↔
      Function.Injective (fun i : Fin l.length => (l.take (i.val + 1)).sum) := by
  exact List.nodup_ofFn

@[category API, AMS 5 11]
theorem validOrdering_length {A : Finset G} {l : List G} (h : ValidOrdering A l) :
    l.length = A.card := by
  rw [← h.2.1, List.toFinset_card_of_nodup h.1]

@[category API, AMS 5 11]
theorem empty_hasValidOrdering : HasValidOrdering (∅ : Finset G) := by
  refine ⟨[], ?_⟩
  simp [ValidOrdering, prefixSums]

@[category API, AMS 5 11]
theorem singleton_hasValidOrdering (a : G) : HasValidOrdering {a} := by
  refine ⟨[a], ?_⟩
  simp [ValidOrdering, prefixSums, List.ofFn_succ]

@[category API, AMS 5 11]
theorem pair_hasValidOrdering (a b : G) (hab : a ≠ b) (hb : b ≠ 0) :
    HasValidOrdering {a, b} := by
  refine ⟨[a, b], ?_⟩
  simp [ValidOrdering, prefixSums, List.ofFn_succ, hab, hb]

@[category API, AMS 5 11]
theorem triple_hasValidOrdering (a b c : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : b ≠ 0) (hc : c ≠ 0) (hs : b + c ≠ 0) :
    HasValidOrdering {a, b, c} := by
  refine ⟨[a, b, c], ?_⟩
  simp [ValidOrdering, prefixSums, List.ofFn_succ, hab, hac, hbc,
    hb, hc, hs, add_assoc]

/-- Every set of at most three nonzero elements of an abelian group has a valid ordering. -/
@[category textbook, AMS 5 11]
theorem erdos_475.variants.card_le_three (A : Finset G) (hzero : (0 : G) ∉ A)
    (hcard : A.card ≤ 3) : HasValidOrdering A := by
  have hcases : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
  rcases hcases with h | h | h | h
  · have hA := Finset.card_eq_zero.mp h
    rw [hA]
    exact empty_hasValidOrdering
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact singleton_hasValidOrdering a
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hb : b ≠ 0 := by
      intro hb
      apply hzero
      simp [← hb]
    exact pair_hasValidOrdering a b hab hb
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have ha : a ≠ 0 := by intro h; apply hzero; simp [← h]
    have hb : b ≠ 0 := by intro h; apply hzero; simp [← h]
    have hc : c ≠ 0 := by intro h; apply hzero; simp [← h]
    by_cases hs : b + c = 0
    · have hs' : a + c ≠ 0 := by
        intro h
        exact hab (add_right_cancel (h.trans hs.symm))
      have h := triple_hasValidOrdering b a c hab.symm hbc hac ha hc hs'
      simpa [Finset.insert_comm] using h
    · exact triple_hasValidOrdering a b c hab hac hbc hb hc hs

/-- Exhaustive search of permutations; true certifies distinct prefix sums. -/
def orderingSearch (l : List G) : Bool :=
  l.permutations'.any (fun r => decide ((prefixSums r).Nodup))

@[category API, AMS 5 11]
theorem orderingSearch_iff (l : List G) (hl : l.Nodup) :
    orderingSearch l = true ↔ HasValidOrdering l.toFinset := by
  simp only [orderingSearch, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, hs⟩
    have hperm := List.mem_permutations'.mp hr
    refine ⟨r, hperm.nodup_iff.mpr hl, ?_, hs⟩
    ext x
    simpa using hperm.mem_iff
  · rintro ⟨r, hr, heq, hs⟩
    refine ⟨r, List.mem_permutations'.mpr ?_, hs⟩
    apply (List.perm_ext_iff_of_nodup hr hl).mpr
    intro x
    have hm := congrArg (fun T : Finset G => x ∈ T) heq
    simpa using hm

end General

/-- The full assertion for a fixed modulus; no primality assumption is hidden. -/
def ModulusStatement (p : ℕ) : Prop :=
  ∀ A : Finset (ZMod p), (0 : ZMod p) ∉ A → HasValidOrdering A

/-- Every nonzero subset of a prime field has a valid ordering. -/
def Statement : Prop := ∀ p : ℕ, Nat.Prime p → ModulusStatement p

/--
Let $p$ be a prime. Given any finite set $A\subseteq \mathbb{F}_p\backslash \{0\}$,
is there always a rearrangement $A=\{a_1,\ldots,a_t\}$ such that all partial sums
$\sum_{1\leq k\leq m}a_{k}$ are distinct, for all $1\leq m\leq t$?
-/
@[category research open, AMS 5 11]
theorem erdos_475 : answer(sorry) ↔
    ∀ p : ℕ, Nat.Prime p → ∀ A : Finset (ZMod p),
      (0 : ZMod p) ∉ A → HasValidOrdering A := by
  sorry

/-- The all-sufficiently-large-primes assertion reported in the literature. -/
def EventuallyStatement : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Nat.Prime p → ModulusStatement p

/-- All nonzero residues, in an explicit computable list. -/
def residueList (p : ℕ) : List (ZMod p) :=
  ((List.range p).map (fun n : ℕ => (n : ZMod p))).filter (fun x => decide (x ≠ 0))

@[category API, AMS 5 11]
theorem mem_residueList (p : ℕ) [NeZero p] (x : ZMod p) :
    x ∈ residueList p ↔ x ≠ 0 := by
  simp only [residueList, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hx
    exact ⟨⟨x.val, ZMod.val_lt x, by simp⟩, hx⟩

@[category API, AMS 5 11]
theorem residueList_nodup (p : ℕ) [NeZero p] : (residueList p).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_range.map_on
  intro a ha b hb heq
  have hav : a < p := List.mem_range.mp ha
  have hbv : b < p := List.mem_range.mp hb
  have hv := congrArg ZMod.val heq
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hv

/-- Check all subsets of nonzero residues and all orderings for each subset. -/
def checkModulus (p : ℕ) : Bool := (residueList p).sublists.all orderingSearch

@[category API, AMS 5 11]
theorem checkModulus_iff (p : ℕ) [NeZero p] :
    checkModulus p = true ↔ ModulusStatement p := by
  simp only [checkModulus, List.all_eq_true]
  constructor
  · intro h A hA
    let l := (residueList p).filter (fun x => decide (x ∈ A))
    have hl : l.Nodup := (residueList_nodup p).filter _
    have hs : l ∈ (residueList p).sublists :=
      List.mem_sublists.mpr List.filter_sublist
    have heq : l.toFinset = A := by
      ext x
      simp only [List.mem_toFinset, l, List.mem_filter, mem_residueList,
        decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro hx
        exact ⟨fun heq => hA (heq ▸ hx), hx⟩
    rw [← heq]
    exact (orderingSearch_iff l hl).mp (h l hs)
  · intro h l hl
    have hs := List.mem_sublists.mp hl
    apply (orderingSearch_iff l ((residueList_nodup p).sublist hs)).mpr
    apply h
    intro hzero
    have hm := hs.subset (List.mem_toFinset.mp hzero)
    exact (mem_residueList p 0).mp hm rfl

/-- A finite test of every prime strictly below N. -/
def checkBelow (N : ℕ) : Bool :=
  (List.range N).all (fun p => if Nat.Prime p then checkModulus p else true)

@[category API, AMS 5 11]
theorem checkBelow_iff (N : ℕ) :
    checkBelow N = true ↔ ∀ p : ℕ, p < N → Nat.Prime p → ModulusStatement p := by
  simp only [checkBelow, List.all_eq_true]
  constructor
  · intro h p hp hprime
    let _ : NeZero p := ⟨hprime.ne_zero⟩
    apply (checkModulus_iff p).mp
    simpa [hprime] using h p (List.mem_range.mpr hp)
  · intro h p hp
    by_cases hprime : Nat.Prime p
    · let _ : NeZero p := ⟨hprime.ne_zero⟩
      simpa [hprime] using (checkModulus_iff p).mpr (h p (List.mem_range.mp hp) hprime)
    · simp [hprime]

/-- Exact formal reduction to a finite check, with the large-prime premise explicit. -/
@[category API, AMS 5 11]
theorem statement_of_eventual_and_check (N : ℕ)
    (hlarge : ∀ p : ℕ, N ≤ p → Nat.Prime p → ModulusStatement p)
    (hsmall : checkBelow N = true) : Statement := by
  intro p hp
  by_cases h : p < N
  · exact (checkBelow_iff N).mp hsmall p h hp
  · exact hlarge p (Nat.le_of_not_gt h) hp

@[category API, AMS 5 11]
theorem statement_iff_eventual_and_check :
    Statement ↔ ∃ N : ℕ,
      (∀ p : ℕ, N ≤ p → Nat.Prime p → ModulusStatement p) ∧ checkBelow N = true := by
  constructor
  · intro h
    refine ⟨0, fun p _ hp => h p hp, ?_⟩
    rfl
  · rintro ⟨N, hlarge, hsmall⟩
    exact statement_of_eventual_and_check N hlarge hsmall

/-- For a certified large-prime threshold, the finite checker is equivalent
to the full question, not merely a sufficient condition. -/
@[category API, AMS 5 11]
theorem statement_iff_checkBelow_of_tail (N : ℕ)
    (hlarge : ∀ p : ℕ, N ≤ p → Nat.Prime p → ModulusStatement p) :
    Statement ↔ checkBelow N = true := by
  constructor
  · intro h
    exact (checkBelow_iff N).mpr (fun p _ hp => h p hp)
  · exact statement_of_eventual_and_check N hlarge

/-- Decide the full statement given a threshold and a proof for all larger primes. -/
def decidableStatementOfTail (N : ℕ)
    (hlarge : ∀ p : ℕ, N ≤ p → Nat.Prime p → ModulusStatement p) :
    Decidable Statement :=
  decidable_of_iff (checkBelow N = true) (statement_iff_checkBelow_of_tail N hlarge).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exhaustive certificate for all primes $p < 8$. -/
@[category test, AMS 5 11]
theorem checkBelow_eight : checkBelow 8 = true := by
  decide +kernel

/-- Every set of nonzero residues modulo a prime $p < 8$ has a valid ordering. -/
@[category textbook, AMS 5 11]
theorem erdos_475.variants.primes_below_eight : ∀ p : ℕ, p < 8 → Nat.Prime p → ModulusStatement p :=
  (checkBelow_iff 8).mp checkBelow_eight

/-- A total sum of zero is permitted by the source's exact statement. -/
@[category test, AMS 5 11]
theorem zero_total_sum_example :
    ValidOrdering ({1, 4} : Finset (ZMod 5)) [1, 4] ∧
      ([1, 4] : List (ZMod 5)).sum = 0 := by
  unfold ValidOrdering
  decide
end Erdos475
