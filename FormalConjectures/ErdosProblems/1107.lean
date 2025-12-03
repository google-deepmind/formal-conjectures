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
# Erdős Problem 1107

*Reference:* [erdosproblems.com/1107](https://www.erdosproblems.com/1107)
-/

namespace Erdos1107

open Nat

/--
A number $n$ is $r$-powerful if for every prime $p$ which divides $n$,
we have $p^r$ divides $n$.
-/
def IsRPowerful (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p ^ r ∣ n

/--
Let $r \ge 2$. Is every large integer the sum of at most $r + 1$ many $r$-powerful numbers?
-/
@[category research open, AMS 11]
theorem erdos_1107 :
    ∀ r ≥ 2, ∃ N, ∀ n ≥ N,
    ∃ s : List ℕ, s.length ≤ r + 1 ∧ (∀ x ∈ s, IsRPowerful r x) ∧ s.sum = n := by
  sorry

end Erdos1107
