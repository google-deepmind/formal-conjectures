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
# Erdős Problem 1094

*Reference:* [erdosproblems.com/1094](https://www.erdosproblems.com/1094)

For all $n\ge 2k$ the least prime factor of $\binom{n}{k}$ is $\le\max(n/k,k)$, with only
finitely many exceptions.  (Status: open.)
-/

namespace Erdos1094

open scoped Nat

/--
Erdős conjectured that there are only finitely many pairs `(n,k)` with `n ≥ 2*k` for which the
least prime factor of the binomial coefficient `Nat.choose n k` exceeds `max (n / k) k`.
Formally: the set of pairs `(n,k)` such that `2*k ≤ n` and `Nat.minFac (Nat.choose n k) >
max (n / k) k` is finite.
-/
@[category research open, AMS 11]
theorem erdos_1094 :
  {p : ℕ × ℕ | (2 * p.snd ≤ p.fst) ∧ Nat.minFac (Nat.choose p.fst p.snd) > max (p.fst / p.snd) p.snd}.Finite ↔
    answer(sorry) := by
  sorry

end Erdos1094
