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
# Grimm's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Grimm%27s_conjecture)
-/

open Function

/--
**Grimm's Conjecture**
If $n, n+1, \dots, n+k-1$ are all composite numbers, then there are $k$ distinct primes $p_i$
such that $p_i$ divides $n + i$ for all $0 \le i \le k-1$.
-/
@[category research open, AMS 11]
theorem grimm_conjecture (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : ∀ i : Fin k, 1 < n + i ∧ ¬ (n + i).Prime) :
    ∃ ps : Fin k ↪ ℕ,  ∀ i : Fin k, (ps i).Prime ∧ ps i ∣ (n + i) := by
  sorry

/--
**Grimm's Conjecture, weaker version**
If $n, n+1, \dots, n+k-1$ are all composite numbers, then their product
has at least $k$ distinct prime divisors.
-/
@[category research open, AMS 11]
theorem grimm_conjecture_weak (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : ∀ i : Fin k, 1 < n + i ∧ ¬ (n + i).Prime) :
    ∃ ps : Fin k ↪ ℕ,  ∀ i : Fin k, (ps i).Prime ∧ ∃ j : Fin k, ps i ∣ (n + j) := by
  sorry
