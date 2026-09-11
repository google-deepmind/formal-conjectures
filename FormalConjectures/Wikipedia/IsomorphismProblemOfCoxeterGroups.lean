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

* `ofTable L`: the Coxeter matrix presented by a list of rows `L : List (List ℕ)`. Every Coxeter
  matrix of finite rank is presented by the list of its rows (`ofTable_surjective`).

## Main results

* `isomorphism_problem_of_coxeter_groups`: the isomorphism problem for Coxeter groups.

## Implementation notes

Decidability is expressed by `ComputablePred`, since classically every proposition is `Decidable`.
The input therefore has to be a `Primcodable` type. Rather than encoding `Σ n, CoxeterMatrix (Fin n)`
we take the input to be a list of rows `L : List (List ℕ)`, and read it as a Coxeter matrix of rank
`L.length` by `ofTable`, which normalises the entries that would violate the axioms of a Coxeter
matrix. Since `ofTable` is computable and surjective, and the list of rows of a Coxeter matrix is
computable from it, deciding the predicate below is equivalent to deciding isomorphism of Coxeter
groups from their Coxeter matrices, whichever reasonable encoding of the latter is chosen.

Mathlib writes the entry $\infty$ of a Coxeter matrix as $0$.

## References

* [B. Mühlherr, *The isomorphism problem for Coxeter groups*](https://doi.org/10.48550/arXiv.math/0506572),
  Problem 1.
* [Y. Santos Rego, P. Schwer, *The galaxy of Coxeter groups*](https://doi.org/10.1016/j.jalgebra.2023.12.006),
  Section 3.2.
* [Wikipedia, *Isomorphism problem of Coxeter groups*](https://en.wikipedia.org/wiki/Isomorphism_problem_of_Coxeter_groups)
-/

namespace IsomorphismProblemOfCoxeterGroups

/-- The symmetrised $(i, j)$ entry of a table of natural numbers, missing entries counting
as $0$. -/
def entry (L : List (List ℕ)) (i j : ℕ) : ℕ :=
  max ((L.getD i []).getD j 0) ((L.getD j []).getD i 0)

@[category API, AMS 20]
theorem entry_comm (L : List (List ℕ)) (i j : ℕ) : entry L i j = entry L j i :=
  max_comm _ _

/-- The Coxeter matrix of rank `L.length` presented by a list of rows `L`: its diagonal entries
are $1$, and its off-diagonal entries are the symmetrised entries of `L`, with $1$ replaced
by $0$. If `L` is the list of rows of a Coxeter matrix `M` then `ofTable L` is `M`, see
`ofTable_surjective`. -/
def ofTable (L : List (List ℕ)) : CoxeterMatrix (Fin L.length) where
  M := Matrix.of fun i j ↦ if i = j then 1 else if entry L i j = 1 then 0 else entry L i j
  isSymm := Matrix.IsSymm.ext fun i j ↦ by
    rcases eq_or_ne i j with rfl | h
    · rfl
    · simp [h, h.symm, entry_comm L j i]
  diagonal i := by simp
  off_diagonal i j h h' := by
    simp only [Matrix.of_apply, if_neg h] at h'
    split_ifs at h' with hk
    exact hk h'

@[category API, AMS 20]
theorem ofTable_apply (L : List (List ℕ)) (i j : Fin L.length) :
    ofTable L i j = if i = j then 1 else if entry L i j = 1 then 0 else entry L i j :=
  rfl

/-- The list of rows of a Coxeter matrix of finite rank. -/
def toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) : List (List ℕ) :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ M i j

@[category API, AMS 20]
theorem length_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) : (toTable M).length = n :=
  List.length_ofFn

@[category API, AMS 20]
theorem getD_ofFn {α : Type*} {n : ℕ} (g : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn g).getD (i : ℕ) d = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), List.getElem_ofFn,
    Option.getD_some]

@[category API, AMS 20]
theorem entry_toTable {n : ℕ} (M : CoxeterMatrix (Fin n)) (i j : Fin n) :
    entry (toTable M) i j = M i j := by
  simp [entry, toTable, M.symmetric j i]

@[category API, AMS 20]
theorem sigma_mk_eq {m n : ℕ} (h : m = n) (X : CoxeterMatrix (Fin m)) (Y : CoxeterMatrix (Fin n))
    (hXY : ∀ i j : Fin m, X i j = Y (Fin.cast h i) (Fin.cast h j)) :
    (⟨m, X⟩ : Σ n, CoxeterMatrix (Fin n)) = ⟨n, Y⟩ := by
  subst h
  obtain ⟨X, _, _, _⟩ := X
  obtain ⟨Y, _, _, _⟩ := Y
  obtain rfl : X = Y := Matrix.ext fun i j ↦ hXY i j
  rfl

/-- Every Coxeter matrix of finite rank is presented by a list of rows. -/
@[category API, AMS 20]
theorem ofTable_surjective :
    Function.Surjective fun L : List (List ℕ) ↦ (⟨L.length, ofTable L⟩ : Σ n, CoxeterMatrix (Fin n)) := by
  rintro ⟨n, M⟩
  refine ⟨toTable M, sigma_mk_eq (length_toTable M) _ _ fun i j ↦ ?_⟩
  rw [ofTable_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, M.diagonal]
  · have hne : Fin.cast (length_toTable M) i ≠ Fin.cast (length_toTable M) j := by
      simpa [Fin.ext_iff] using hij
    have h₁ := entry_toTable M (Fin.cast (length_toTable M) i) (Fin.cast (length_toTable M) j)
    simp only [Fin.val_cast] at h₁
    rw [if_neg hij, h₁, if_neg (M.off_diagonal _ _ hne)]

/--
**The isomorphism problem for Coxeter groups.** Is there an algorithm which, given two Coxeter
matrices $M$ and $M'$ of finite rank, decides whether the Coxeter groups $W(M)$ and $W(M')$ are
isomorphic?

Coxeter matrices are given as lists of rows, see `ofTable` and `ofTable_surjective`.
-/
@[category research open, AMS 3 20]
theorem isomorphism_problem_of_coxeter_groups :
    answer(sorry) ↔ ComputablePred fun p : List (List ℕ) × List (List ℕ) ↦
      Nonempty ((ofTable p.1).Group ≃* (ofTable p.2).Group) := by
  sorry

end IsomorphismProblemOfCoxeterGroups
