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

import FormalConjecturesUtil

/-!
# Erdős Problem 421

*References:*
- [erdosproblems.com/421](https://www.erdosproblems.com/421)
- [Pratt26] K. Pratt, [A proof of Erdős Problem 421](https://www.erdosproblems.com/static/421-Pratt.pdf).
-/

open Set

namespace Erdos421

/--
There exists a sequence $1 \le d_1 < d_2 < \dots$ with density 1 such that all products
$\prod_{u \le i \le v} d_i$ are distinct. This was solved affirmatively; see [Pratt26]. -/
@[category research solved, AMS 11]
theorem erdos_421 : answer(True) ↔
    ∃ (d : ℕ → ℕ), StrictMono d ∧ 1 ≤ d 0 ∧ HasDensity (Set.range d) 1 ∧
    {(u, v) : ℕ × ℕ | u ≤ v}.InjOn fun (u, v) => ∏ i ∈ Finset.Icc u v, d i := by
  sorry

end Erdos421
