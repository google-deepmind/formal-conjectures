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
# Erdős Problem 421

*Reference:* [erdosproblems.com/421](https://www.erdosproblems.com/421)
-/

open Set

namespace Erdos421

/--
Is there a sequence $1 \le d_1 < d_2 < \dots$ with density 1 such that all products
$\prod_{u \le i \le v} d_i$ are distinct? -/
@[category research open, AMS 11]
theorem erdos_421 : answer(sorry) ↔
    ∃ (d : ℕ → ℕ), StrictMono d ∧ 1 ≤ d 0 ∧ HasDensity (Set.range d) 1 ∧
    {(u, v) : ℕ × ℕ | u ≤ v}.InjOn fun (u, v) => ∏ i ∈ Finset.Icc u v, d i := by
  sorry

/--
For the sequence $d_i = i + 1$ (the natural numbers starting from 2), consecutive products
$\prod_{u \le i \le v} d_i = (v+1)!/(u!)$ are distinct for distinct intervals,
providing a natural candidate (though this sequence does not have density 1).
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/421", AMS 11]
theorem erdos_421.variants.known_result :
    ∃ (d : ℕ → ℕ), StrictMono d ∧ 1 ≤ d 0 ∧
    {(u, v) : ℕ × ℕ | u ≤ v}.InjOn fun (u, v) => ∏ i ∈ Finset.Icc u v, d i := by
  sorry

end Erdos421
