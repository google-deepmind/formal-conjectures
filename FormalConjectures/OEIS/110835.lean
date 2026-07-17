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

/-!
# A110835: Smallest m > 0 such that there are no primes between n*m and n*(m+1) inclusive.

Sierpinski's conjecture (1958) is precisely that a(n) >= n for all n.

*References:*
- [A110835](https://oeis.org/A110835)
-/

namespace OeisA110835

open Nat Set

/-- 
The primary defining sequence `a`.
a(n) is the smallest $m > 0$ such that there are no primes between $n \cdot m$ and $n \cdot (m+1)$ inclusive.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let is_prime_free_interval (m : ℕ) : Prop :=
    ∀ p : ℕ, Nat.Prime p → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1))
  let S : Set ℕ := {m : ℕ | m > 0 ∧ is_prime_free_interval m}
  sInf S

/--
Sierpinski's conjecture (1958) is precisely that a(n) >= n for all n.
-/
@[category research open, AMS 11]
theorem main_conjecture : ∀ n > 0, a n ≥ n := by
  sorry

end OeisA110835
