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
# Erdős Problem 730

*References:*
  - [erdosproblems.com/730](https://www.erdosproblems.com/730)
  - [A129515](https://oeis.org/A129515)
-/
private abbrev S :=
  {(n, m) : ℕ × ℕ | n < m ∧ ((2*n).choose n).primeFactors = ((2*m).choose m).primeFactors}


/--
Are there infinitely many pairs of integers $n < m$ such that $\binom{2n}{n}$
and $\binom{2m}{m}$ have the same set of prime divisors?
-/
@[category research open, AMS 11]
theorem erdos_730 : S.Infinite ↔ answer(sorry) := by
  sorry

/--
For example, $(87,88)$ and $(607,608)$ are such pairs.
-/
@[category high_school, AMS 11]
theorem erdos_730.variants.explicit_pairs :
    {(87, 88), (607, 608)} ⊆ S := by
  sorry

/--
Show that for all $n$, the binomial coefficient $\binom{2n}{n}$ is even.
-/
@[category high_school, AMS 11]
theorem erdos_730.variants.two_div_forall (n : ℕ) (h : 0 < n) : 2 ∣ (2*n).choose n := by
  sorry

/--
In every known example $(n, m) ∈ S$, we have $m = n + 1$.
-/
@[category research open, AMS 11]
theorem erdos_730.variants.delta_one (n m : ℕ) (h : (n, m) ∈ S) : m = n + 1 := by
  sorry
