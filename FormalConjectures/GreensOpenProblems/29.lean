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
# Ben Green's Open Problem 29

*References:*
- [Ben Green's Open Problem 29](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.29)
- [Gr12] Green, Ben. "What is... an approximate group." Notices Amer. Math. Soc 59.5 (2012): 655-656.
- [Br13] Breuillard, Emmanuel, Ben Green, and Terence Tao. "Small doubling in groups."
  Erdős Centennial. Berlin, Heidelberg: Springer Berlin Heidelberg, 2013. 129-151.
  [arXiv:1301.7718](https://arxiv.org/abs/1301.7718)
- [Sa10] Sanders, Tom. "On a nonabelian Balog–Szemerédi-type lemma." Journal of the Australian
  Mathematical Society 89.1 (2010): 127-132.
- [CrSi10] Croot, Ernie, and Olof Sisask. "A probabilistic technique for finding almost-periods of
  convolutions." Geometric and functional analysis 20.6 (2010): 1367-1396.

The printed Problem 29 includes the stronger hypothesis `S ⊆ A`; that strengthened variant is
false (see `green_29.subset_counterexample`). The open problem is the version without `S ⊆ A`,
following [Br13, Theorem 6.5 and the question after it].
-/

@[expose] public section

open scoped Pointwise

namespace Green29

/-- **Ben Green's Open Problem 29 / the open question after [Br13, Theorem 6.5].**
Suppose that `A` is a `K`-approximate group (not necessarily abelian). Can one find a set
`S` (not necessarily contained in `A`) with `|S| ≫ K^{-O(1)} |A|` and `S ^ 8 ⊆ A ^ 4`?

This is open even in the abelian case. The stronger variant requiring `S ⊆ A` is false; see
`green_29.subset_counterexample`. The known result with `|S| ≫_K |A|` is `green_29.variant`. -/
@[category research open, question, AMS 20]
theorem green_29 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
        1 ≤ K → IsApproximateSubgroup K (A : Set G) →
          ∃ S : Finset G, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
            S ^ 8 ⊆ A ^ 4 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The strengthened variant of Green's Problem 29 requiring `S ⊆ A` is false. A counterexample
is given, for arbitrarily large finite groups `H`, by
`A = ({-1} × H) ∪ ({1} × H) ∪ {(0, 1)}` in `Multiplicative ℤ × H`. -/
@[category research solved, question, AMS 20,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/green-29-counterexample/blob/1cbf80c3d5a333b2b79c203c0d60129924c8c712/lean/Green29FC.lean#L280-L287"]
theorem green_29.subset_counterexample :
    ¬ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
        1 ≤ K → IsApproximateSubgroup K (A : Set G) →
          ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
          S ^ 8 ⊆ A ^ 4 := by
  sorry

/-- The known result [Br13, Theorem 6.5; CrSi10; Sa10]: for each `K` there is `c = c(K) > 0`
such that every `K`-approximate group `A` has a set `S` (not necessarily contained in `A`) with
`|S| ≫_K |A|` and `S ^ 8 ⊆ A ^ 4`. The open problem asks for `c` independent of `K`. -/
@[category research solved, AMS 20]
theorem green_29.variant :
    ∀ K : ℝ, 1 ≤ K →
      ∃ c : ℝ, 0 < c ∧ -- Allow c to depend on K.
        ∀ {G : Type*} [Group G] [DecidableEq G] (A : Finset G),
          IsApproximateSubgroup K (A : Set G) →
            ∃ S : Finset G, -- No S ⊆ A requirement in this variant.
              c * (A.card : ℝ) ≤ (S.card : ℝ) ∧
              S ^ 8 ⊆ A ^ 4 := by
  sorry

end Green29
