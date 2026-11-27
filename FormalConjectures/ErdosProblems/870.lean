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
# Erdős Problem 870

## References

- [erdosproblems.com/870](https://www.erdosproblems.com/870)
- [ErNa88] Erdős and Nathanson, *Partitions of bases into disjoint unions of bases*.
  J. Number Theory 29 (1988), 1–9.
- [Tur26] Turturean, *Additive bases with many representations and no minimal subbasis*.
  [Lean formalization](https://github.com/davidturturean/erdos-870).
-/

@[expose] public section

open Filter

namespace Erdos870

/-- Nonempty representations by at most `k` positive elements of `A`.
A multiset counts each representation once, irrespective of the order of its terms. -/
def representations (A : Set ℕ) (k n : ℕ) : Set (Multiset ℕ) :=
  {s | 0 < s.card ∧ s.card ≤ k ∧ (∀ a ∈ s, 0 < a ∧ a ∈ A) ∧ s.sum = n}

/-- With zero summands allowed, there are no nonempty representations. -/
@[category test, AMS 11]
theorem representations_order_zero (A : Set ℕ) (n : ℕ) : representations A 0 n = ∅ := by
  ext s
  simp only [representations, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hpos, hle, -⟩
  omega

/-- An at-most-`k) asymptotic basis represents every sufficiently large natural number. -/
def IsBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ᶠ n in atTop, (representations A k n).Nonempty

/-- A basis is minimal if every proper subset fails to be a basis of the same order. -/
def IsMinimalBasis (A : Set ℕ) (k : ℕ) : Prop :=
  IsBasis A k ∧ ∀ B ⊂ A, ¬ IsBasis B k

set_option linter.style.formal_proof_palomar false in
/--
For each $k \geq 3$, does there exist $c > 0$ such that any asymptotic basis of
order $k$ with at least $c \log n$ representations of every sufficiently large
$n$ contains a minimal asymptotic basis of order $k$?

The representation count follows the problem page and [Tur26]. The question in
[ErNa88] instead uses the maximum number of pairwise disjoint representations.
Turturean proved a negative answer for every $k \geq 3$.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/davidturturean/erdos-870/blob/a732dee4fbbef41e8a300aef264a3bc1bf505862/Erdos870/Main.lean#L6"]
theorem erdos_870 :
    ¬ ∀ k : ℕ, 3 ≤ k →
      ∃ c : ℝ, 0 < c ∧ ∀ A : Set ℕ, IsBasis A k →
        (∀ᶠ n : ℕ in atTop, c * Real.log (n : ℝ) ≤ (Nat.card (representations A k n) : ℝ)) →
        ∃ B ⊆ A, IsMinimalBasis B k := by
  sorry

end Erdos870
