import Mathlib

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a set `A ⊆ M`. -/
def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, B.toSet ⊆ A ∧ n = ∑ i ∈ B, i}

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddComplete [Preorder M] (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A
