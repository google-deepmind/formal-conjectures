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
# The Shearer–Kleitman conjecture on orthogonal symmetric chain decompositions

The `n`-cube is the poset of all subsets of `{1, …, n}` ordered by inclusion. It
can be partitioned into `binomial n (n / 2)` chains, the minimum possible number
(this is the width of the poset, by Sperner's theorem). A *symmetric chain
decomposition* (SCD) is such a partition into `binomial n (n / 2)` *symmetric*
chains: saturated chains whose smallest and largest members have sizes summing to
`n` (so the chain is symmetric about the middle level `n / 2`).

Two SCDs are *orthogonal* if any chain of the one and any chain of the other share
at most a single element. Shearer and Kleitman conjectured in 1979 that the
`n`-cube has `n / 2 + 1` pairwise orthogonal symmetric chain decompositions, and
constructed two of them.

We model a subset of `{1, …, n}` as a `Finset (Fin n)`, a chain as a
`Finset (Finset (Fin n))` (a set of subsets that is totally ordered by inclusion),
and an SCD as a `Finset` of such chains.

*References:*
- [Wikipedia: Symmetric chain decomposition](https://en.wikipedia.org/wiki/Symmetric_chain_decomposition)
- [DJMS20] R. Däubel, S. Jäger, T. Mütze, and M. Scheucher, *On orthogonal
  symmetric chain decompositions*, Electron. J. Combin. 26(3) (2019/2020), no. P3.64.
  [doi:10.37236/8531](https://doi.org/10.37236/8531). Best known bounds: four
  pairwise orthogonal SCDs for `n ≥ 60`, and five pairwise edge-disjoint SCDs for
  `n ≥ 90`.
- [SK79] J. B. Shearer and D. J. Kleitman, *Probabilities of independent choices
  being ordered*, Stud. Appl. Math. 60 (1979), 271–276. (Original conjecture.)
-/

open Finset

namespace ShearerKleitman

variable {n : ℕ}

/-- A `Finset` of subsets of `Fin n` is a *chain* in the `n`-cube if it is totally
ordered by inclusion. -/
def IsChain' (C : Finset (Finset (Fin n))) : Prop :=
  (C : Set (Finset (Fin n))).Pairwise (fun A B => A ⊆ B ∨ B ⊆ A)

/-- A chain `C` is *saturated* if every size between its smallest and largest
member occurs. Together with `IsChain'` (which forces distinct members to have
distinct sizes) this makes the sizes an unbroken range with exactly one member
per size, i.e. consecutive members differ in size by exactly one. -/
def IsSaturated (C : Finset (Finset (Fin n))) : Prop :=
  ∀ k : ℕ, (∃ A ∈ C, A.card ≤ k) → (∃ B ∈ C, k ≤ B.card) →
    ∃ A ∈ C, A.card = k

/-- A chain is *symmetric* if it is saturated and the sizes of its smallest and
largest members sum to `n` (so it is symmetric about the middle level `n / 2`). -/
def IsSymmetricChain (C : Finset (Finset (Fin n))) : Prop :=
  C.Nonempty ∧ IsChain' C ∧ IsSaturated C ∧
    ∃ A ∈ C, ∃ B ∈ C, (∀ D ∈ C, A.card ≤ D.card) ∧ (∀ D ∈ C, D.card ≤ B.card) ∧
      A.card + B.card = n

/-- A *symmetric chain decomposition* (SCD) of the `n`-cube: a `Finset` `𝒟` of
chains that are all symmetric, are pairwise disjoint, and together cover every
subset of `Fin n` (partition of the whole power set). Necessarily
`𝒟.card = binomial n (n / 2)`. -/
def IsSCD (𝒟 : Finset (Finset (Finset (Fin n)))) : Prop :=
  (∀ C ∈ 𝒟, IsSymmetricChain C) ∧
    (𝒟 : Set (Finset (Finset (Fin n)))).PairwiseDisjoint id ∧
    𝒟.biUnion id = Finset.univ

/-- Two chains share at most one element. -/
def ShareAtMostOne (C D : Finset (Finset (Fin n))) : Prop :=
  (C ∩ D).card ≤ 1

/-- Two SCDs are *orthogonal* if every chain of the one and every chain of the
other share at most a single element. -/
def Orthogonal (𝒟 ℰ : Finset (Finset (Finset (Fin n)))) : Prop :=
  ∀ C ∈ 𝒟, ∀ D ∈ ℰ, ShareAtMostOne C D

/--
**The Shearer–Kleitman conjecture (1979).** For every `n`, the `n`-cube has
`n / 2 + 1` pairwise orthogonal symmetric chain decompositions.
-/
@[category research open, AMS 5 6]
theorem shearer_kleitman (n : ℕ) :
    ∃ F : Fin (n / 2 + 1) → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → Orthogonal (F i) (F j)) := by
  sorry

namespace variants

/--
Shearer and Kleitman constructed two orthogonal SCDs, so the conjecture holds for
the count `2` (for every `n`). This is the base case they established in 1979.
-/
@[category research solved, AMS 5 6]
theorem two_orthogonal_scds (n : ℕ) :
    ∃ F : Fin 2 → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → Orthogonal (F i) (F j)) := by
  sorry

/--
[DJMS20] constructed four pairwise orthogonal symmetric chain decompositions of
the `n`-cube for all `n ≥ 60`, the current best bound towards the conjecture.
-/
@[category research solved, AMS 5 6]
theorem four_orthogonal_scds (n : ℕ) (hn : 60 ≤ n) :
    ∃ F : Fin 4 → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → Orthogonal (F i) (F j)) := by
  sorry

/-- Two chains are *edge-disjoint* if they share no covering pair `(A, A ∪ {x})`,
i.e. no edge of the cube lies in both. This is slightly weaker than orthogonality.
-/
def EdgeDisjoint (C D : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ C, ∀ B ∈ C, A ⊆ B → B.card = A.card + 1 →
    ¬ (A ∈ D ∧ B ∈ D)

/-- Two SCDs are edge-disjoint if all their chains are pairwise edge-disjoint. -/
def EdgeDisjointSCD (𝒟 ℰ : Finset (Finset (Finset (Fin n)))) : Prop :=
  ∀ C ∈ 𝒟, ∀ D ∈ ℰ, EdgeDisjoint C D

/--
[DJMS20] constructed five pairwise edge-disjoint symmetric chain decompositions
of the `n`-cube for all `n ≥ 90`. Edge-disjointness is a weaker notion than
orthogonality.
-/
@[category research solved, AMS 5 6]
theorem five_edge_disjoint_scds (n : ℕ) (hn : 90 ≤ n) :
    ∃ F : Fin 5 → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → EdgeDisjointSCD (F i) (F j)) := by
  sorry

end variants

end ShearerKleitman
