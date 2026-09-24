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

Two decompositions are *orthogonal* if any chain of the one and any chain of the
other share at most a single element. Shearer and Kleitman conjectured in 1979 that
the `n`-cube has `n / 2 + 1` pairwise orthogonal decompositions into the minimum
number of chains, and constructed two of them. The chains in this conjecture need
not be symmetric.

Symmetric chains are the natural tool, but strict orthogonality is impossible for
two *symmetric* chain decompositions once `n ≥ 1`: the maximal chain running from
`∅` to the full ground set is forced into every SCD, and two such chains already
share both endpoints. Spink and [DJMS20] therefore work with *almost orthogonal*
SCDs, which exempt exactly that one maximal pair (allowing it to meet in `∅` and the
full set). For `n ≥ 5` a family of almost-orthogonal SCDs can be turned into
orthogonal chain decompositions by "moving `∅`", so the two forms carry the same
count. We state both (`shearer_kleitman` and `shearer_kleitman_symmetric`).

We model a subset of `{1, …, n}` as a `Finset (Fin n)`, a chain as a
`Finset (Finset (Fin n))` (a set of subsets that is totally ordered by inclusion),
and an SCD as a `Finset` of such chains.

*References:*
- [Wikipedia: Symmetric chain decomposition](https://en.wikipedia.org/wiki/Symmetric_chain_decomposition)
- [Spink] H. Spink, *Orthogonal symmetric chain decompositions of hypercubes*,
  [arXiv:1706.08545](https://arxiv.org/abs/1706.08545). Introduces the "almost
  orthogonal" notion (Def. 2.1) used here, and constructs three almost-orthogonal
  SCDs for `n` large (Thm. 3.1).
- [DJMS20] R. Däubel, S. Jäger, T. Mütze, and M. Scheucher, *On orthogonal
  symmetric chain decompositions*, Electron. J. Combin. 26(3) (2019/2020), no. P3.64.
  [doi:10.37236/8531](https://doi.org/10.37236/8531). Building on [Spink], the best
  known bounds: four pairwise almost-orthogonal SCDs for `n ≥ 60`, and five pairwise
  edge-disjoint SCDs for `n ≥ 90`.
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

/-- A *chain decomposition* of the `n`-cube into the minimum number of chains: a
`Finset` `𝒟` of chains (each totally ordered by inclusion, not required to be
symmetric or saturated) that are pairwise disjoint, cover the whole power set, and
number exactly `binomial n (n / 2)` — the minimum possible (the width of the cube,
by Sperner). Every SCD is a chain decomposition, but not conversely. (No member is
empty: exactly `binomial n (n / 2)` chains must cover all `2 ^ n` subsets, leaving
no room for an empty one.) -/
def IsChainDecomposition (𝒟 : Finset (Finset (Finset (Fin n)))) : Prop :=
  (∀ C ∈ 𝒟, IsChain' C) ∧
    (𝒟 : Set (Finset (Finset (Fin n)))).PairwiseDisjoint id ∧
    𝒟.biUnion id = Finset.univ ∧
    𝒟.card = n.choose (n / 2)

/-- Two chains share at most one element. -/
def ShareAtMostOne (C D : Finset (Finset (Fin n))) : Prop :=
  (C ∩ D).card ≤ 1

/-- A chain is *maximal* if it is a symmetric chain that spans the whole cube from
bottom to top, i.e. it contains both `∅` and the full ground set `Finset.univ`
(equivalently, it is the symmetric chain of size `n + 1`). In every SCD (for
`n ≥ 1`) exactly one chain is maximal: the symmetric chain through `∅`, whose
largest member therefore has card `n`. -/
def IsMaximalChain (C : Finset (Finset (Fin n))) : Prop :=
  IsSymmetricChain C ∧ ∅ ∈ C ∧ Finset.univ ∈ C

/-- Two SCDs are *almost orthogonal* if every chain of the one and every chain of
the other share at most a single element, **except** that the two (unique) maximal
chains are allowed to meet in both their forced common endpoints `∅` and `univ`.

This is the notion introduced by [Spink] and used by [DJMS20]: no two SCDs are
strictly orthogonal (`Orthogonal` below) for `n ≥ 1`, since the maximal chain
through `∅` is forced into every SCD and any two such chains already share both `∅`
and `univ`. The endpoint exemption is [Spink, Def. 2.1] and [DJMS20, §1] ("the two
unique chains of size `n + 1` are only allowed to intersect in their minimal and
maximal elements `∅` and `[n]`"). For two maximal chains the intersection is forced
to contain `{∅, univ}`, so `⊆` here is in fact equality. -/
def AlmostOrthogonal (𝒟 ℰ : Finset (Finset (Finset (Fin n)))) : Prop :=
  ∀ C ∈ 𝒟, ∀ D ∈ ℰ, ShareAtMostOne C D ∨
    (IsMaximalChain C ∧ IsMaximalChain D ∧ C ∩ D ⊆ {∅, Finset.univ})

/-- Two SCDs are (strictly) *orthogonal* if every chain of the one and every chain
of the other share at most a single element. Note no two SCDs can be strictly
orthogonal for `n ≥ 1` (see `AlmostOrthogonal`); the conjecture and the known
constructions are about `AlmostOrthogonal`. -/
def Orthogonal (𝒟 ℰ : Finset (Finset (Finset (Fin n)))) : Prop :=
  ∀ C ∈ 𝒟, ∀ D ∈ ℰ, ShareAtMostOne C D

/--
**The Shearer–Kleitman conjecture (1979).** For every `n`, the `n`-cube has
`n / 2 + 1` pairwise orthogonal decompositions into the minimum number of chains.

This is the conjecture as Shearer and Kleitman stated it, and as [Spink]/[DJMS20]
restate it: the chains here need not be symmetric, and orthogonality is the strict
`Orthogonal` (every two chains share at most one element). Non-symmetric chains
avoid the obstruction that makes strict orthogonality impossible for *symmetric*
decompositions (e.g. [DJMS20] exhibit three orthogonal decompositions of `Q₄` using
non-symmetric chains). The symmetric working notion is `shearer_kleitman_symmetric`
below; for `n ≥ 5` a family of almost-orthogonal SCDs yields orthogonal chain
decompositions by "moving `∅`", so the two forms have the same count asymptotically.
-/
@[category research open, AMS 5 6]
theorem shearer_kleitman (n : ℕ) :
    ∃ F : Fin (n / 2 + 1) → Finset (Finset (Finset (Fin n))),
      (∀ i, IsChainDecomposition (F i)) ∧ (∀ i j, i ≠ j → Orthogonal (F i) (F j)) := by
  sorry

/--
**The Shearer–Kleitman conjecture, symmetric form.** For every `n`, the `n`-cube
has `n / 2 + 1` pairwise almost-orthogonal *symmetric* chain decompositions.

This is the notion Spink and [DJMS20] actually work with: strict orthogonality is
impossible for two symmetric chain decompositions once `n ≥ 1` (their forced
maximal chains share `∅` and `univ`), so one relaxes to `AlmostOrthogonal`, which
exempts exactly that pair. This form implies the classical `shearer_kleitman` for
`n ≥ 5` (by moving `∅`), and is what the constructed lower bounds below establish.
-/
@[category research open, AMS 5 6]
theorem shearer_kleitman_symmetric (n : ℕ) :
    ∃ F : Fin (n / 2 + 1) → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → AlmostOrthogonal (F i) (F j)) := by
  sorry

namespace variants

/--
Shearer and Kleitman constructed two almost-orthogonal SCDs, so the conjecture
holds for the count `2` (for every `n`). This is the base case they established in
1979.
-/
@[category research solved, AMS 5 6]
theorem two_almost_orthogonal_scds (n : ℕ) :
    ∃ F : Fin 2 → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → AlmostOrthogonal (F i) (F j)) := by
  sorry

/--
[DJMS20] constructed four pairwise almost-orthogonal symmetric chain
decompositions of the `n`-cube for all `n ≥ 60`, the current best bound towards the
conjecture. (The bound `60` is what their product construction yields, i.e.
sufficient, not known to be necessary.)
-/
@[category research solved, AMS 5 6]
theorem four_almost_orthogonal_scds (n : ℕ) (hn : 60 ≤ n) :
    ∃ F : Fin 4 → Finset (Finset (Finset (Fin n))),
      (∀ i, IsSCD (F i)) ∧ (∀ i j, i ≠ j → AlmostOrthogonal (F i) (F j)) := by
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
