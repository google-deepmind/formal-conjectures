import Mathlib

variable {M : Type*} [AddCommMonoid M]

open scoped List
open Filter Topology Set

/-- The set of subset sums of a set `A ⊆ M`. -/
def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, B.toSet ⊆ A ∧ n = ∑ i ∈ B, i}

/-- The set of subset sums of a sequence `ℕ → M`. -/
def subseqSums (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, B.toSet.InjOn A ∧ n = ∑ i ∈ B, A i}

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddComplete [Preorder M] (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
distinct terms of `A`. -/
def IsAddCompleteNatSeq [Preorder M] (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums A

/-- A sequence `A` is strongly complete if `fun m => A (n + m)` is still complete for all `n`. -/
def IsAddStronglyCompleteNatSeq [Preorder M] (A : ℕ → M) : Prop :=
  ∀ n, IsAddCompleteNatSeq (fun m => A (n + m))

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' [Preorder M] (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

/-- We define a sequence `f` by the formula `f n = n.fib - (- 1) ^ n`. -/
def f (n : ℕ) : ℕ := if Even n then n.fib - 1 else n.fib + 1

def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ k, c * n k < n (k + 1)

/-- Every lacunary sequence is strictly increasing. -/
lemma IsLacunary.strictMono {n : ℕ → ℕ} (hn : IsLacunary n) : StrictMono n := by
  refine strictMono_nat_of_lt_succ fun k => (Nat.cast_lt (α := ℝ)).mp ?_
  obtain ⟨c, hc⟩ := hn
  refine (hc.2 k).trans_le' ?_
  grw [hc.1, one_mul]

/-- The sequence `f` is Lacunary. -/
theorem erdos_346.f_isLacunary : IsLacunary f := by sorry

/-- Erdős and Graham [ErGr80] remark that it is easy to see that if `A (n + 1) / A n > (1 + √5) / 2`
then the second property is automatically satisfied. -/
theorem erdos_346.gt_goldenRatio_not_IsAddComplete {A : ℕ → ℕ}
    (hA : ∀ n, (1 + √5) / 2 * A n < A (n + 1)) {B : Set ℕ} (hB : B.Infinite) :
    ¬ IsAddComplete (range A \ B) := by
  sorry

/-- Erdős and Graham [ErGr80] also says that it is not hard to construct very irregular sequences
satisfying the aforementioned properties. -/
theorem erdos_346.example : ∃ A : ℕ → ℕ, IsLacunary A ∧ IsAddStronglyCompleteNatSeq A ∧
    ∀ B : Set ℕ, B.Infinite → ¬ IsAddComplete (range A \ B) ∧
    liminf (fun n => A (n + 1) / (2 : ℝ)) atTop = 1 ∧
    limsup (fun n => A (n + 1) / (A n : ENNReal)) atTop = ⊤ := by
  sorry
