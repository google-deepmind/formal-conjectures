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
# Erdős Problem 396

*Reference:* [erdosproblems.com/396](https://www.erdosproblems.com/396)
-/

namespace Erdos396

open Nat

/--
Is it true that for every $k$ there exists $n$ such that
$$\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}?$$
-/
@[category research open, AMS 11]
def erdos_396 : (∀ k : ℕ, ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n) ↔ answer(sorry) := by
  sorry


-- TODO(firsching): formalise the additional material

end Erdos396
