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

- [Er51] Erdős, P., _Some problems and results in elementary number theory_.
  Publ. Math. Debrecen (1951), 103–109.
- [Er57] Erdős, P., _Some unsolved problems_, 1957.
- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. **6** (1961), 221–254.
- [BaCh47] Bambah, R. P. and Chowla, S., _On numbers which can be expressed
  as a sum of two squares_. Proc. Nat. Inst. Sci. India (1947), 101–103.
- [Ri82] Richards, I., _On the gaps between numbers which are sums of two
  squares_. Adv. in Math. (1982), 1–2.
- [DEKKM22] Dietmann, R., Elsholtz, C., Kalmynin, A., Konyagin, S., and
  Maynard, J., _Longer Gaps Between Values of Binary Quadratic Forms_.
  International Mathematics Research Notices (2023), 10313–10349.

## OEIS

- [A256435](https://oeis.org/A256435) Differences of consecutive integers
  that are sums of two squares.
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

/--
Erdős's lower bound on gaps in the sum-of-two-squares sequence [Er51]:
there exist infinitely many $k$ such that
$n_{k+1} - n_k \gg \frac{\log n_k}{\sqrt{\log \log n_k}}$,
i.e. there exists a constant $C > 0$ such that for infinitely many $k$,
$n_{k+1} - n_k \geq C \cdot \frac{\log n_k}{\sqrt{\log \log n_k}}$.
-/
@[category research solved, AMS 11]
theorem erdos_222.variants.erdos_lower_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ᶠ k in atTop,
      ((sumTwoSqSeq (k + 1) : ℝ) - (sumTwoSqSeq k : ℝ)) ≥
        C * (Real.log (sumTwoSqSeq k : ℝ) /
          Real.sqrt (Real.log (Real.log (sumTwoSqSeq k : ℝ)))) := by
  sorry

/--
Dietmann–Elsholtz–Kalmynin–Konyagin–Maynard (2022) improvement [DEKKM22]:
the limsup of $(n_{k+1} - n_k) / \log n_k$ is at least $0.868\ldots$,
improving the constant $1/4$ from Richards [Ri82].
-/
@[category research solved, AMS 11]
theorem erdos_222.variants.dekkm22_lower_bound :
    ∀ δ : ℝ, δ > 0 → ∃ᶠ k in atTop,
      ((sumTwoSqSeq (k + 1) : ℝ) - (sumTwoSqSeq k : ℝ)) ≥
        (0.868 - δ) * Real.log (sumTwoSqSeq k : ℝ) := by
  sorry

end Erdos222
