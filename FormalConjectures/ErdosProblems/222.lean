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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 222

*Reference:* [erdosproblems.com/222](https://www.erdosproblems.com/222)

Let $n_1 < n_2 < \cdots$ be the sequence of integers which are the sum of two
squares. Explore the behaviour of the consecutive differences $n_{k+1} - n_k$.

## References

- [BaCh47] Bambah, R. P. and Chowla, S. (1947), on the upper bound
  $n_{k+1} - n_k \ll n_k^{1/4}$.
- [Ri82] Richards, I. (1982),
  $\limsup_{k \to \infty} (n_{k+1} - n_k) / \log n_k \geq 1/4$.
- [DEKKM22] Dietmann, R., Elsholtz, C., Kalmynin, A., Konyagin, S., and
  Maynard, J. (2022), improved the constant to $0.868\ldots$.
-/

open Filter

namespace Erdos222

/-- A natural number is a sum of two squares if it can be written as $a^2 + b^2$
for some natural numbers $a$ and $b$. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- The $k$-th element (0-indexed) of the increasing enumeration of natural
numbers that are sums of two squares: $0, 1, 2, 4, 5, 8, 9, 10, 13, \ldots$ -/
noncomputable def sumTwoSqSeq (k : ℕ) : ℕ :=
  Nat.nth IsSumOfTwoSquares k

/--
Bambah–Chowla (1947) upper bound on gaps in the sum-of-two-squares sequence [BaCh47]:
the consecutive differences satisfy $n_{k+1} - n_k \ll n_k^{1/4}$,
i.e. there exists a constant $C > 0$ such that eventually
$n_{k+1} - n_k \leq C \cdot n_k^{1/4}$.
-/
@[category research solved, AMS 11]
theorem erdos_222 :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ k in atTop,
      ((sumTwoSqSeq (k + 1) : ℝ) - (sumTwoSqSeq k : ℝ)) ≤
        C * (sumTwoSqSeq k : ℝ) ^ ((1 : ℝ) / 4) := by
  sorry

/--
Richards (1982) lower bound on gaps in the sum-of-two-squares sequence [Ri82]:
for every $\delta > 0$, there are infinitely many $k$ such that
$n_{k+1} - n_k \geq (1/4 - \delta) \cdot \log n_k$.

This is equivalent to $\limsup_{k \to \infty} (n_{k+1} - n_k) / \log n_k \geq 1/4$.
-/
@[category research solved, AMS 11]
theorem erdos_222.variants.lower_bound :
    ∀ δ : ℝ, δ > 0 → ∃ᶠ k in atTop,
      ((sumTwoSqSeq (k + 1) : ℝ) - (sumTwoSqSeq k : ℝ)) ≥
        (1 / 4 - δ) * Real.log (sumTwoSqSeq k : ℝ) := by
  sorry

end Erdos222
