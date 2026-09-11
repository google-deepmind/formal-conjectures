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

import FormalConjecturesUtil

/-!
# The isomorphism problem for Coxeter groups

Is there an algorithm which, given two Coxeter matrices of finite rank, decides whether the
corresponding Coxeter groups are isomorphic?

## Main definitions

* `FinCoxeterMatrix`: a Coxeter matrix of finite rank, `Σ n, CoxeterMatrix (Fin n)`.
* `equivTable`: the bijection between `FinCoxeterMatrix` and Coxeter tables (`IsCoxeterTable`),
  the lists of rows of Coxeter matrices. It gives `FinCoxeterMatrix` its `Primcodable` structure.

## Main results

* `isomorphism_problem_of_coxeter_groups`: the isomorphism problem for Coxeter groups.

## Implementation notes

Decidability is expressed by `ComputablePred`, since classically every proposition is `Decidable`.
This requires a `Primcodable` structure on `FinCoxeterMatrix`, obtained by encoding a Coxeter
matrix by the list of its rows. Any encoding from which this list can be computed primitive
recursively, and conversely, is primitive recursively isomorphic to this one, so the statement does
not depend on this choice.

Mathlib writes the entry $\infty$ of a Coxeter matrix as $0$. Restricting to matrices indexed by
`Fin n` loses no generality, as reindexing does not change the isomorphism type of the Coxeter
group (`CoxeterMatrix.reindexGroupEquiv`).

## References

## References

* [B. Mühlherr, *The isomorphism problem for Coxeter groups*](https://doi.org/10.48550/arXiv.math/0506572),
  Problem 1.
* [Y. Santos Rego, P. Schwer, *The galaxy of Coxeter groups*](https://doi.org/10.1016/j.jalgebra.2023.12.006),
  Section 3.2.
* [Wikipedia, *Isomorphism problem of Coxeter groups*](https://en.wikipedia.org/wiki/Isomorphism_problem_of_Coxeter_groups)
-/

namespace IsomorphismProblemOfCoxeterGroups

open Primrec

/-- A Coxeter matrix of finite rank. -/
abbrev FinCoxeterMatrix := Σ n : ℕ, CoxeterMatrix (Fin n)

/- Bounded quantification is primitive recursive. -/
@[category API, AMS 3]
theorem foldr_decide_and {β : Type*} (p : β → Prop) [DecidablePred p] (l : List β) :
    l.foldr (fun b s ↦ decide (p b ∧ s = true)) true = decide (∀ b ∈ l, p b) := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.foldr_cons, ih]; simp

@[category API, AMS 3]
theorem primrecPred_forall_mem_list {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {R : α → β → Prop} [∀ a b, Decidable (R a b)]
    (hf : Primrec f) (hR : PrimrecRel R) : PrimrecPred fun a ↦ ∀ b ∈ f a, R a b := by
  obtain ⟨_, hR'⟩ := (hR.comp (α := α × β × Bool) fst (fst.comp snd)).and
    (Primrec.eq.comp (snd.comp snd) (const true))
  have hh : Primrec₂ fun (a : α) (p : β × Bool) ↦ decide (R a p.1 ∧ p.2 = true) := by
    unfold Primrec₂
    exact hR'.of_eq fun _ ↦ decide_eq_decide.mpr Iff.rfl
  have h : Primrec fun a ↦ (f a).foldr (fun b s ↦ decide (R a b ∧ s = true)) true :=
    list_foldr hf (const true) hh
  exact ⟨inferInstance, h.of_eq fun a ↦
    (foldr_decide_and (R a) (f a)).trans (decide_eq_decide.mpr Iff.rfl)⟩

@[category API, AMS 3]
theorem primrecPred_forall_lt {α : Type*} [Primcodable α] {f : α → ℕ} {R : α → ℕ → Prop}
    [∀ a n, Decidable (R a n)] (hf : Primrec f) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∀ n < f a, R a n :=
  (primrecPred_forall_mem_list (list_range.comp hf) hR).of_eq fun _ ↦ by simp

/- Coxeter tables. -/

/-- The $(i, j)$ entry of a table of natural numbers, with default value $0$. -/
def entry (L : List (List ℕ)) (i j : ℕ) : ℕ := (L.getD i []).getD j 0

@[category API, AMS 3]
theorem primrec_entry : Primrec fun p : List (List ℕ) × ℕ × ℕ ↦ entry p.1 p.2.1 p.2.2 :=
  (list_getD 0).comp ((list_getD ([] : List ℕ)).comp fst (fst.comp snd)) (snd.comp snd)

/-- A *Coxeter table* is a square symmetric table of natural numbers whose entries are equal to
$1$ exactly on the diagonal. These are the lists of rows of Coxeter matrices of finite rank, see
`equivTable`. -/
def IsCoxeterTable (L : List (List ℕ)) : Prop :=
  (∀ row ∈ L, row.length = L.length) ∧
    ∀ i < L.length, ∀ j < L.length, entry L i j = entry L j i ∧ (i = j ↔ entry L i j = 1)

instance : DecidablePred IsCoxeterTable := fun L ↦ by
  unfold IsCoxeterTable
  infer_instance

@[category API, AMS 3]
theorem primrecPred_isCoxeterTable : PrimrecPred IsCoxeterTable := by
  have hsquare : PrimrecPred fun L : List (List ℕ) ↦ ∀ row ∈ L, row.length = L.length :=
    primrecPred_forall_mem_list Primrec.id
      (Primrec.eq.comp (list_length.comp snd) (list_length.comp fst))
  have e₁ : Primrec fun r : (List (List ℕ) × ℕ) × ℕ ↦ entry r.1.1 r.1.2 r.2 :=
    primrec_entry.comp ((fst.comp fst).pair ((snd.comp fst).pair snd))
  have e₂ : Primrec fun r : (List (List ℕ) × ℕ) × ℕ ↦ entry r.1.1 r.2 r.1.2 :=
    primrec_entry.comp ((fst.comp fst).pair (snd.pair (snd.comp fst)))
  have hdiag : PrimrecPred fun r : (List (List ℕ) × ℕ) × ℕ ↦ r.1.2 = r.2 :=
    Primrec.eq.comp (snd.comp fst) snd
  have hone : PrimrecPred fun r : (List (List ℕ) × ℕ) × ℕ ↦ entry r.1.1 r.1.2 r.2 = 1 :=
    Primrec.eq.comp e₁ (const 1)
  have hbody : PrimrecRel fun (q : List (List ℕ) × ℕ) (j : ℕ) ↦
      entry q.1 q.2 j = entry q.1 j q.2 ∧ (q.2 = j ↔ entry q.1 q.2 j = 1) :=
    (Primrec.eq.comp e₁ e₂).and (((hdiag.and hone).or (hdiag.not.and hone.not)).of_eq
      fun _ ↦ iff_iff_and_or_not_and_not.symm)
  have hrow : PrimrecRel fun (L : List (List ℕ)) (i : ℕ) ↦ ∀ j < L.length,
      entry L i j = entry L j i ∧ (i = j ↔ entry L i j = 1) :=
    primrecPred_forall_lt (list_length.comp fst) hbody
  exact hsquare.and (primrecPred_forall_lt list_length hrow)

instance : Primcodable {L : List (List ℕ) // IsCoxeterTable L} :=
  Primcodable.subtype primrecPred_isCoxeterTable


/- Coxeter matrices of finite rank are in bijection with Coxeter tables. -/
@[category API, AMS 3]
theorem getD_ofFn {α : Type*} {n : ℕ} (g : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn g).getD (i : ℕ) d = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), List.getElem_ofFn,
    Option.getD_some]

/-- The list of rows of a Coxeter matrix of finite rank. -/
def toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) : List (List ℕ) :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ M i j

@[category API, AMS 20]
theorem length_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) : (toTable M).length = n :=
  List.length_ofFn

@[category API, AMS 20]
theorem entry_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) (i j : Fin n) :
    entry (toTable M) i j = M i j := by
  simp only [entry, toTable, getD_ofFn]

@[category API, AMS 20]
theorem isCoxeterTable_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    IsCoxeterTable (toTable M) := by
  refine ⟨fun row hrow ↦ ?_, fun i hi j hj ↦ ?_⟩
  · simp only [toTable, List.mem_ofFn] at hrow
    obtain ⟨k, rfl⟩ := hrow
    simp [length_toTable]
  · rw [length_toTable] at hi hj
    rw [entry_toTable M ⟨i, hi⟩ ⟨j, hj⟩, entry_toTable M ⟨j, hj⟩ ⟨i, hi⟩]
    refine ⟨M.symmetric _ _, fun h ↦ ?_, fun h ↦ ?_⟩
    · subst h
      exact M.diagonal _
    · by_contra h'
      exact M.off_diagonal _ _ (fun e ↦ h' (congrArg Fin.val e)) h

/-- The Coxeter matrix whose list of rows is a given Coxeter table. -/
def ofTable (L : List (List ℕ)) (hL : IsCoxeterTable L) : CoxeterMatrix (Fin L.length) where
  M := Matrix.of fun i j ↦ entry L i j
  isSymm := Matrix.IsSymm.ext fun i j ↦ (hL.2 j j.2 i i.2).1
  diagonal i := (hL.2 i i.2 i i.2).2.mp rfl
  off_diagonal i j h h' := h (Fin.ext ((hL.2 i i.2 j j.2).2.mpr h'))

@[category API, AMS 20]
theorem entry_ofTable (L : List (List ℕ)) (hL : IsCoxeterTable L) (i j : Fin L.length) :
    ofTable L hL i j = entry L i j :=
  rfl

@[category API, AMS 20]
theorem FinCoxeterMatrix.ext {m n : ℕ} (h : m = n) (X : CoxeterMatrix (Fin m))
    (Y : CoxeterMatrix (Fin n)) (hXY : ∀ i j : Fin m, X i j = Y (Fin.cast h i) (Fin.cast h j)) :
    (⟨m, X⟩ : FinCoxeterMatrix) = ⟨n, Y⟩ := by
  subst h
  obtain ⟨X, _, _, _⟩ := X
  obtain ⟨Y, _, _, _⟩ := Y
  obtain rfl : X = Y := Matrix.ext fun i j ↦ hXY i j
  rfl

/-- Coxeter matrices of finite rank are in bijection with Coxeter tables. -/
def equivTable : FinCoxeterMatrix ≃ {L : List (List ℕ) // IsCoxeterTable L} where
  toFun M := ⟨toTable M.2, isCoxeterTable_toTable M.2⟩
  invFun L := ⟨L.1.length, ofTable L.1 L.2⟩
  left_inv := by
    rintro ⟨n, M⟩
    exact FinCoxeterMatrix.ext (length_toTable M) _ _ fun i j ↦
      entry_toTable M (Fin.cast (length_toTable M) i) (Fin.cast (length_toTable M) j)
  right_inv := by
    rintro ⟨L, hL⟩
    refine Subtype.ext (List.ext_getElem (length_toTable _) fun i _ hi ↦ ?_)
    replace hi : i < L.length := hi
    have hrow : L[i].length = L.length := hL.1 _ (List.getElem_mem hi)
    refine List.ext_getElem (by simp [toTable, hrow]) fun j _ hj ↦ ?_
    replace hj : j < L[i].length := hj
    simp [toTable, entry_ofTable, entry, List.getD_eq_getElem?_getD, hj]

/-- A Coxeter matrix of finite rank is encoded by the list of its rows. -/
instance : Primcodable FinCoxeterMatrix := Primcodable.ofEquiv _ equivTable

/--
**The isomorphism problem for Coxeter groups.** Is there an algorithm which, given two Coxeter
matrices $M$ and $M'$ of finite rank, decides whether the Coxeter groups $W(M)$ and $W(M')$ are
isomorphic?

Equivalently, is it decidable whether $W(M)$ has a subset $S$ such that $(W(M), S)$ is a Coxeter
system of type $M'$?
-/
@[category research open, AMS 3 20]
theorem isomorphism_problem_of_coxeter_groups :
    answer(sorry) ↔ ComputablePred fun p : FinCoxeterMatrix × FinCoxeterMatrix ↦
      Nonempty (p.1.2.Group ≃* p.2.2.Group) := by
  sorry

end IsomorphismProblemOfCoxeterGroups
