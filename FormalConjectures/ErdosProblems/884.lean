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
# Erdős Problem 884

*Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)

[Er98] Erdős, P., _Some of my new and almost new problems and results in
combinatorial number theory_ (1998).
-/

open Finset

namespace Erdos884

/--
Is it true that, for any $n$, if $d_1 < \cdots < d_t$ are the divisors of $n$, then
$$\sum_{1 \leq i < j \leq t} \frac{1}{d_j - d_i} \ll 1 + \sum_{1 \leq i < t} \frac{1}{d_{i+1} - d_i},$$
where the implied constant is absolute? [Er98]

The double sum over all pairs of divisors is bounded (up to an absolute constant)
by $1$ plus the sum over consecutive divisor gaps. Two divisors are consecutive
if no other divisor of $n$ lies strictly between them.

See also problem #144.
-/
@[category research open, AMS 11]
theorem erdos_884 :
    answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (∑ p ∈ (n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2),
        (1 : ℝ) / ((p.2 : ℝ) - (p.1 : ℝ))) ≤
      C * (1 + ∑ p ∈ (n.divisors ×ˢ n.divisors).filter (fun p =>
        p.1 < p.2 ∧ ∀ e ∈ n.divisors, ¬(p.1 < e ∧ e < p.2)),
        (1 : ℝ) / ((p.2 : ℝ) - (p.1 : ℝ))) := by
  sorry

end Erdos884
