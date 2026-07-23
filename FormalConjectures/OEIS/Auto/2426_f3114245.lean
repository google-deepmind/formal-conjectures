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

open Polynomial

/--
A002426: Central trinomial coefficients: largest coefficient of $(1 + x + x^2)^n$.
This is the coefficient of $x^n$ in the expansion of $(1 + x + x^2)^n$.
-/
noncomputable def A002426 (n : ℕ) : ℕ :=
  ((1 + X + X^2 : Polynomial ℕ) ^ n).coeff n

open Int

/--
Conjecture: An integer n > 3 is prime if and only if a(n) == 1 (mod n^2).
We have verified this for n up to 8*10^5, and proved that a(p) == 1 (mod p^2)
for any prime p > 3 (cf. A277640). - Zhi-Wei Sun, Nov 30 2016
-/
theorem oeis_2426_conjecture_0 :
  ∀ n : ℕ, 3 < n → (n.Prime ↔ (A002426 n : ℤ) ≡ 1 [ZMOD (n^2 : ℤ)]) := by
  sorry
