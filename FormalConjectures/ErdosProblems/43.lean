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
If `A` and `B` are Sidon sets in `{1, ..., N}` with disjoint difference sets such that
$(A-A)\cap(B-B)=\{0\}$ then is it true that
$$\binom{\lvert A\rvert}{2}+\binom{\lvert B\rvert}{2}\leq\binom{f(N)}{2}+O(1),$$
where $f(N)$ is the maximum possible size of a Sidon set in \{1,\ldots,N\}?
-/
@[category research open, AMS 05 11]
theorem erdos_43 :
    (∃ C : ℝ, ∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      (A - A) ∩ (B - B) = {0} →
      A.card.choose 2 + B.card.choose 2 ≤ (maxSidonSetSize N).choose 2 + C) ↔
      answer(sorry) := by
  sorry

/--
If `A` and `B` are equal-sized Sidon sets in `{1, ..., N}` with disjoint difference sets such
that $(A-A)\cap(B-B)=\{0\}$, then is it true that
$$\binom{\lvert A\rvert}{2}+\binom{\lvert B\rvert}{2}\leq(1-c)\binom{f(N)}{2}$$
for some constant $c>0$?
-/
@[category research open, AMS 05 11]
theorem erdos_43_equal_size :
    (∃ᵉ (c > 0), ∀ (N : ℕ) (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon A.toSet →
      IsSidon B.toSet →
      A.card = B.card →
      (A - A) ∩ (B - B) = {0} →
      A.card.choose 2 + B.card.choose 2 ≤ (1 - c) * (maxSidonSetSize N).choose 2) ↔
      answer(sorry) := by
  sorry
