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
# Erdős Problem 1161

*Reference:* [erdosproblems.com/1161](https://www.erdosproblems.com/1161)
-/

namespace Erdos1161

/-- $f_k(n)$ is the number of elements of $S_n$ of order $k$. -/
noncomputable def f (k n : ℕ) : ℕ :=
  { σ : Equiv.Perm (Fin n) | orderOf σ = k }.ncard

/--
Let $f_k(n)$ count the number of elements of $S_n$ of order $k$. For which values of $k$ will
$f_k(n)$ be maximal?
-/
@[category research open, AMS 20]
theorem erdos_1161 (n : ℕ) :
    answer(sorry) = { k : ℕ | ∀ j : ℕ, f j n ≤ f k n } := by
  sorry

end Erdos1161
