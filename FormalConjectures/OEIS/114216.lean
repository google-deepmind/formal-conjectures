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
# Largest odd divisor of a(n-1) + prime(n)

a(0)=0; thereafter a(n) = largest odd divisor of a(n-1) + prime(n).

*References:*
- [A114216](https://oeis.org/A114216)
-/

namespace OeisA114216

/--
The primary defining sequence `a`.
a(n) is the largest odd divisor of a(n-1) + prime(n).
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 =>
    let p_n : ℕ := Nat.nth Nat.Prime n'
    let prev_a : ℕ := a n'
    let sum_val : ℕ := prev_a + p_n
    let nu_2 : ℕ := padicValNat 2 sum_val
    sum_val / (2 ^ nu_2)

@[category test, AMS 11]
lemma test_a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by
  simp [a]

/--
Is a(33900) the last term equal to 1?
-/
@[category research open, AMS 11]
theorem main_conjecture :
  answer(sorry) ↔ ∀ n > 33900, a n ≠ 1 := by
  sorry

end OeisA114216
