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

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2


theorem a_zero : A053000 0 = 2 := by
  sorry

theorem a_one : A053000 1 = 1 := by
  sorry

theorem a_two : A053000 2 = 1 := by
  sorry

theorem a_three : A053000 3 = 2 := by
  sorry


/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  sorry
