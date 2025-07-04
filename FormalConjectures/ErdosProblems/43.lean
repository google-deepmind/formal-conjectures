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
  sSup {n | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon A.toSet ∧ A.card = n}

/--
If `A` and `B` are Sidon sets in `{1, ..., N}` with disjoint difference sets,
is the sum of unordered pair counts bounded by that of an optimal Sidon set up to `O(1)`?
-/
@[category research open, AMS 11 05]
theorem erdos_43 :
    ∃ C : ℝ, ∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      (A ×ˢ A).image (λ p => p.1 - p.2) ∩
        (B ×ˢ B).image (λ p => p.1 - p.2) = ∅ →
      ((A.card * (A.card - 1) + B.card * (B.card - 1)) / 2 : ℝ) ≤
        (maxSidonSetSize N * (maxSidonSetSize N - 1) / 2 : ℝ) + C := by
  sorry

/--
If `A` and `B` are equal-sized Sidon sets with disjoint difference sets,
can the sum of pair counts be bounded by a strict fraction of the optimum?
-/
@[category research open, AMS 11 05]
theorem erdos_43_equal_size :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      A.card = B.card →
      (A ×ˢ A).image (λ p => p.1 - p.2) ∩
        (B ×ˢ B).image (λ p => p.1 - p.2) = ∅ →
      ((A.card * (A.card - 1) + B.card * (B.card - 1)) / 2 : ℝ) ≤
        (1 - c) * (maxSidonSetSize N * (maxSidonSetSize N - 1) / 2 : ℝ) := by
  sorry
