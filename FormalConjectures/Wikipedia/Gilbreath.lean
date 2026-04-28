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
# Gilbreath's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture)
-/

namespace Gilbreath

/--
**Gilbreath's nth difference**, $d^n$
Let $d^0(n) = p_n$ and $d^k(n) = |d^{k-1}(n+1) - d^{k-1}(n)|
-/
noncomputable def d : ℕ → (ℕ → ℕ)
  | 0 => fun n ↦ n.nth Nat.Prime
  | k + 1 => fun n ↦ Int.natAbs (d k (n + 1) - d k n)

open Gilbreath

/--
**Gilbreath's conjecture**
Gilbreath's conjecture states that every term in the sequence $d^k_0$ for $k > 0$ is equal to 1.
-/
@[category research open, AMS 11]
theorem gilbreath_conjecture (k : ℕ+) : d k 0 = 1 := by
  sorry

end Gilbreath
