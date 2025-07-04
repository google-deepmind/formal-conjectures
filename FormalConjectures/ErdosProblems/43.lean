/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 43: Disjoint Differences in Sidon Sets

Let `f(N)` denote the maximum possible size of a Sidon set in `{1, ..., N}`.

Suppose `A, B ⊆ {1, ..., N}` are both Sidon sets and their difference sets are disjoint:
\[
(A - A) ∩ (B - B) = ∅
\]

Is it true that
\[
\binom{|A|}{2} + \binom{|B|}{2} ≤ \binom{f(N)}{2} + O(1) ?
\]

Furthermore, if `|A| = |B|`, can this be improved to
\[
\binom{|A|}{2} + \binom{|B|}{2} ≤ (1 - c) \binom{f(N)}{2}
\]
for some constant `c > 0`?

Find the link to the problem [here](https://www.erdosproblems.com/43).

-/

/-- The maximum size of a Sidon set in `{1, ..., N}`. -/
noncomputable def maxSidonSetSize (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsSidon A.toSet ∧ A.card = n}

/--
If `A` and `B` are Sidon subsets of `{1, ..., N}` with disjoint difference sets,
is it true that the sum of their pair counts is at most the pair count of the optimal Sidon set,
up to an additive constant?
-/
@[category research open, AMS 11B]
theorem erdos_43 :
    (∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Icc 1 N →
      B ⊆ Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      ((A ×ˢ A).image (λ p => p.1 - p.2) ∩
       (B ×ˢ B).image (λ p => p.1 - p.2)).card = 0 →
      ∃ C : ℝ,
        (choose A.card 2 + choose B.card 2 : ℝ) ≤
          choose (maxSidonSetSize N) 2 + C) ↔ answer(sorry) := by
  sorry

/--
If `A` and `B` are equal-sized Sidon subsets of `{1, ..., N}` with disjoint differences,
can we improve the bound to be a strict proportion below the optimal?
-/
@[category research open, AMS 11B]
theorem erdos_43_equal_size :
    (∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Icc 1 N →
      B ⊆ Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      A.card = B.card →
      ((A ×ˢ A).image (λ p => p.1 - p.2) ∩
       (B ×ˢ B).image (λ p => p.1 - p.2)).card = 0 →
      ∃ c : ℝ, 0 < c ∧
        (choose A.card 2 + choose B.card 2 : ℝ) ≤
          (1 - c) * choose (maxSidonSetSize N) 2) ↔ answer(sorry) := by
  sorry
