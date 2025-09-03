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
# Erdős Problem 249

*Reference:* [erdosproblems.com/249](https://www.erdosproblems.com/249)
-/

open scoped Nat

namespace Erdos249

/--
Is
$$\sum_{n} \frac{φ(n)}{2^n}$$
irrational? Here $\phi$ is the Euler totient function.
-/
@[category research open, AMS 11]
theorem erdos_249 : Irrational (∑' n : ℕ, (φ n) / (2 ^ n)) ↔ answer(sorry) := by
  sorry

end Erdos249
