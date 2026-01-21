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

/--
If $2^x$ and $3^x$ are integers, then $x$ must be an integer.
-/
@[category research open, AMS 11 13]
theorem mathoverflow_17560 {x : ℝ} (hx : ∃ m : ℕ, 2 ^ x = m) (hx' : ∃ m : ℕ, 3 ^ x = m) :
    ∃ m : ℤ, x = m := by
  sorry

/--
If for each natural number $n$ the number $n^x$ is an integer then $x$ must also be an integer.
-/
@[category graduate, AMS 11 13]
theorem mathoverflow_17560.variants.with_5 {x : ℝ} (hx : ∀ n : ℕ, ∃ m : ℕ, n ^ x = m) :
    ∃ m : ℤ, x = m := by
  sorry

/--
If $2^x$, $3^x$ and $5^x$ are integers, then $x$ must be an integer.
-/
@[category graduate, AMS 11 13]
theorem mathoverflow_17560.variants.with_5 {x : ℝ} (hx : ∃ m : ℕ, 2 ^ x = m)
    (hx' : ∃ m : ℕ, 3 ^ x = m) : ∃ m : ℤ, x = m := by
  sorry
