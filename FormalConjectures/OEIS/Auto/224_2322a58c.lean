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
open Finset

/--
A000224: Number of squares $\bmod n$.
This is the cardinality of the set $\{k^2 \bmod n \mid k \in \{0, 1, \dots, n-1\}\}$.
-/
noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))


theorem a_one : A000224 1 = 1 := by sorry

theorem a_two : A000224 2 = 2 := by sorry

theorem a_three : A000224 3 = 2 := by sorry

theorem a_four : A000224 4 = 2 := by sorry


/--
Conjecture: n^2 == 1 (mod a(n)*(a(n)-1)) if and only if n is an odd prime.
-/
theorem oeis_a000224_conjecture_ordowski {n : ℕ} (h_n : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  sorry
