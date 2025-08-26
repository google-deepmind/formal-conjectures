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
# Erdős Problem 257

*Reference:* [erdosproblems.com/257](https://www.erdosproblems.com/257)
-/

namespace Erdos257

/--
Let $A\subseteq\mathbb{N}$ be an infinite set. Is
$$
\sum_{n\in A} \frac{1}{2^n - 1}
$$
irrational?
-/
@[category research open, AMS 11]
theorem erdos_257 : (∀ (A : Set ℕ), A.Infinite →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) ↔ answer(sorry) := by
  sorry

/--
Show that
$$
\sum_{n} \frac{1}{2^n - 1} = \sum_{n} \frac{d(n)}{2^n},
$$
where $d(n)$ is the number of divisors of $n$.
-/
@[category undergraduate, AMS 11]
theorem erdos_257.variants.tsum_top_eq :
    ∑' n, 1 / (2 ^ n - 1 : ℝ) = ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  sorry

/--
Show that
$$
\sum_{n} \frac{d(n)}{2^n}
$$
is irrational.

[Er48] Erdős, P., _On arithmetical properties of Lambert series_. J. Indian Math. Soc. (N.S.) (1948), 63-66.
-/
@[category research solved, AMS 11]
theorem erdos_257.variants.tsum_top :
    Irrational <| ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  sorry

end Erdos257
