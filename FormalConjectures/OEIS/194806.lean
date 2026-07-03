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
# Conjectures associated with A194806

The set of all products of elements from a Finset S.

A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$
such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.

*References:*
- [A194806](https://oeis.org/A194806)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA194806


open Finset Nat

/-- The set of all products of elements from a Finset S. -/
def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

/--
A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$
such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let T_n := Icc 1 n

    -- The set of subsets $S \subseteq T_n$ such that $T_n \subseteq S \cdot S$.
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)

    -- Proof that $T_n$ is guaranteed to be a valid subset, ensuring `valid_subsets` is non-empty.
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      -- 1. T_n ∈ T_n.powerset (i.e., T_n ⊆ T_n)
      apply mem_powerset.mpr; rfl
      -- 2. T_n ⊆ set_prod T_n
      intro k hk

      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩

      -- We show k = k * 1 is in set_prod T_n
      -- set_prod T_n is the image of T_n × T_n under multiplication.
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      -- Show that (k, 1) ∈ T_n × T_n
      · exact mem_product.mpr ⟨hk, h1⟩
      -- Show that k * 1 = k
      · exact Nat.mul_one k

    have h_nonempty : valid_subsets.Nonempty := ⟨T_n, T_n_is_valid⟩

    let sizes := valid_subsets.image Finset.card

    -- The min' function requires proof that the finset is non-empty.
    have h_sizes_nonempty : sizes.Nonempty := h_nonempty.image Finset.card

    -- We return the minimum card of all valid subsets.
    sizes.min' h_sizes_nonempty


@[category test, AMS 11]
lemma a_one : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 3 := by rfl

@[category test, AMS 11]
lemma a_five : a 5 = 4 := by rfl


/--
The set of all products of elements from a Finset S.

A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$
such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/194806.wip.lean#L472"]
theorem target_theorem_0
  : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C := by
    sorry

end OeisA194806
