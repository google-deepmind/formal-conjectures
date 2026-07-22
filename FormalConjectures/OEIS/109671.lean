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
# OEIS A109671

$a(1)=1$; thereafter, $a(2n)=a(n)$, $a(2n+1)$ is the smallest positive number such that $|a(2n+1)-a(2n-1)|=a(n)$.
Conjecture: Does the sequence contain every positive integer?

*References:*
- [A109671](https://oeis.org/A109671)
-/

namespace OeisA109671

/--
The primary defining sequence `a`.
$a(1)=1$; thereafter, $a(2n)=a(n)$, $a(2n+1)$ is the smallest positive number such that $|a(2n+1)-a(2n-1)|=a(n)$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n % 2 = 0 then
    a (n / 2)
  else
    let k := (n - 1) / 2
    let a_prev_odd := a (n - 2)
    let a_k := a k
    if a_prev_odd > a_k then
      a_prev_odd - a_k
    else
      a_prev_odd + a_k
termination_by n

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by native_decide

/--
Does the sequence contain every positive integer (cf. A169741)?
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ m : ℕ, 0 < m → ∃ n : ℕ, 0 < n ∧ a n = m := by
  sorry

end OeisA109671
