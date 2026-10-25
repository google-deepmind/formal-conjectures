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
# Erdős Problem 679

*References:*
- [erdosproblems.com/679](https://www.erdosproblems.com/679)
- [Er79d] P. Erdős, Some unconventional problems in number theory.
  Acta Math. Acad. Sci. Hungar. 33 (1979), 71–80.
-/

@[expose] public section

open Filter Real

namespace Erdos679

/--
Let $\epsilon>0$ and $\omega(n)$ count the number of distinct prime factors of $n$.
Are there infinitely many values of $n$ such that
$$\omega(n-k) < (1+\epsilon)\frac{\log k}{\log\log k}$$
for all $k<n$ which are sufficiently large depending on $\epsilon$ only?
-/
@[category research open, question, AMS 11]
theorem erdos_679.parts.i :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∃ᶠ n : ℕ in atTop,
      ∀ k : ℕ, K < k → k < n →
        (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) <
          (1 + ε) * log k / log (log k) := by
  sorry

/--
Can one show the stronger version with
$$\omega(n-k) < \frac{\log k}{\log\log k}+O(1)$$
is false?

DottedCalculator disproved this strengthening. For every additive constant $C$ and cutoff $K$,
all sufficiently large $n$ admit $K<k<n$ violating the bound.
-/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at "https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean"]
theorem erdos_679.parts.ii (C : ℝ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ k < n, K < k ∧
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  sorry

end Erdos679
