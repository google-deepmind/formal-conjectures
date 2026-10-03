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
# Number of integers $0 < k < n$ such that $p = k + \phi(n - k)$ and $2(n - p) + 1$ are both prime

*References:*
- [A234809](https://oeis.org/A234809)
-/

namespace OeisA234809

/--
The primary defining sequence `a`.
$a(n)$ is the number of integers $0 < k < n$ such that $p = k + \phi(n - k)$
and $2(n - p) + 1$ are both prime, where $\phi$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    let p := k + (n - k).totient
    if p.Prime ∧ Nat.Prime (2 * (n - p) + 1) then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 < n) : 0 < a n := by
  sorry

end OeisA234809
