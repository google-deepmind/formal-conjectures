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
# Erdős Problem 5

*Reference:* [erdosproblems.com/5](https://www.erdosproblems.com/5)

This problem concerns the set of limit points of the normalized prime gap sequence
$(p_{n+1} - p_n) / \log n$, where $p_n$ denotes the $n$-th prime. The conjecture,
posed in several papers of Erdős [Er55c, Er57, Er61, Er65b, Er85c, Er90, Er97c],
asserts that this set of limit points equals $[0, \infty]$.
-/

open Filter Nat Real

namespace Erdos5

/--
The normalized prime gap at index $n$ (0-indexed):
$$\frac{p_{n+1} - p_n}{\log(n+1)}$$
where $p_n = \texttt{nth Nat.Prime}\; n$ is the $n$-th prime (so $p_0 = 2$, $p_1 = 3$, ...).
We use $n+1$ in the denominator so that $\log$ is evaluated at a positive argument.
-/
noncomputable def normalizedPrimeGap (n : ℕ) : ℝ :=
  ((nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ)) / Real.log ((n : ℝ) + 1)

/--
Let $p_n$ denote the $n$-th prime. Let $S$ be the set of limit points of the sequence
$(p_{n+1} - p_n) / \log n$.
The conjecture [Er55c, Er57, Er61, Er65b, Er85c, Er90, Er97c] asserts $S = [0, \infty]$,
i.e., every value $C \in [0, \infty]$ is attained as a limit along some subsequence.

Formally (for finite $C$): for every $C \geq 0$ there exists a strictly increasing
sequence of indices $n_1 < n_2 < \cdots$ such that
$$(p_{n_i+1} - p_{n_i}) / \log n_i \to C \quad \text{as } i \to \infty.$$

Known results toward this conjecture:
- $\infty \in S$ (Westzynthius 1931): prime gaps are unbounded relative to $\log n$.
- $0 \in S$ (Goldston–Pintz–Yıldırım 2009): normalized gaps can be arbitrarily small.
- $S$ has positive Lebesgue measure (Erdős 1955; Ricci 1956).
- $S$ contains arbitrarily large finite numbers (Hildebrand–Maier 1988).
- $[0, c] \subseteq S$ for some $c > 0$ (Pintz 2016).
- At least $12.5\%$ of $[0, \infty)$ belongs to $S$ (Banks–Freiberg–Maynard 2016).
- At least $1/3$ of $[0, \infty)$ belongs to $S$, and $S$ has bounded gaps (Merikoski 2020).
-/
@[category research open, AMS 11]
theorem erdos_5 :
    ∀ C : ℝ, 0 ≤ C →
      ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun i => normalizedPrimeGap (f i)) atTop (nhds C) := by
  sorry

end Erdos5
