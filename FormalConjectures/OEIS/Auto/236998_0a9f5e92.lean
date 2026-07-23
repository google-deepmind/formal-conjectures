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

open Nat Finset

/--
A236998: a(n) = |{0 < k < n/2: phi(k)*phi(n-k) is a square}|, where phi(.) is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

/--
OEIS A236998 Conjecture (i) states that a(n) > 0 for all n > 8.
This theorem formalizes the claim about the verified range:
"For n from 9 to 2*10^6, a(n) > 0."
%C A236998 a(n) > 0 for all n > 8 has been verified for n up to 2*10^6.
-/
theorem oeis_236977_conjecture_1 (n : ℕ) (h_n : 9 ≤ n ∧ n ≤ 2 * 10^6) : a n > 0 := by
  sorry
