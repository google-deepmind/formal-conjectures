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
# Erdős Problem 43
*Reference:* [erdosproblems.com/43](https://www.erdosproblems.com/43)

-/

open scoped Pointwise


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
      (A - A) ∩ (B - B) = ∅ →
      A.card.choose 2 + B.card.choose 2 ≤ (maxSidonSetSize N).choose 2 + C := by
  sorry

/--
If `A` and `B` are equal-sized Sidon sets with disjoint difference sets,
can the sum of pair counts be bounded by a strict fraction of the optimum?
-/
@[category research open, AMS 11 05]
theorem erdos_43_equal_size :
    ∃ᵉ (c > 0), ∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      A.card = B.card →
      (A - A) ∩ (B - B) = ∅ →
      A.card.choose 2 + B.card.choose 2 ≤ (1 - c) *(maxSidonSetSize N).choose 2 := by
  sorry
