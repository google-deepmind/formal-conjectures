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

import FormalConjecturesUtil

/-!
# Erdős Problem 1140

*Reference:* [erdosproblems.com/1140](https://www.erdosproblems.com/1140)
-/

namespace Erdos1140

/-- `n - 2x^2` is prime for every `x` with `2x^2 < n`. -/
def AllPrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

/--
Do there exist infinitely many $n$ such that $n-2x^2$ is prime for all $x$ with $2x^2<n$?
-/
@[category research open, AMS 11]
theorem erdos_1140 : answer(sorry) ↔ { n : ℕ | AllPrime n }.Infinite := by
  sorry

end Erdos1140
