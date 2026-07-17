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
import Mathlib.Data.Nat.Prime.Nth

/-!
# A110854

$a(n) = \mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$,
where $\mathrm{prime}(k)$ is the $k$-th prime number.

*References:*
- [A110854](https://oeis.org/A110854)
-/

namespace OeisA110854

open Nat

/--
The primary defining sequence `a`.
a(n) is $\mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let p (k : ℕ) : ℤ := (Nat.nth Nat.Prime (k - 1)).cast
  if n = 0 then 0
  else p (2 * n + 2) - p (2 * n + 1) - p (2 * n) + p (2 * n - 1)

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by
  dsimp [a]
  norm_num

/--
Do the absolute values cover A004275?
A004275 is the set of all differences between two prime numbers.
The conjecture asks whether every possible difference between two prime numbers occurs as the absolute value of some term $a(n)$.
-/
@[category research open, AMS 11]
theorem main_conjecture :
  ∀ d > 0, (∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ d = (p1 - p2 : ℤ).natAbs) →
  ∃ n > 0, d = (a n).natAbs := by
  sorry

end OeisA110854
