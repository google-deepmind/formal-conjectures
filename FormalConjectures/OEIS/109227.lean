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
import Mathlib.Data.Nat.Prime.Basic

/-!
# OEIS A109227

Binary strings that have 1's where primes occur, 0's elsewhere and every term ends with the $n$-th prime index.
Conjecture A109227: $a(2)$ and $a(121)$ are primes. Are there any more?

*References:*
- [A109227](https://oeis.org/A109227)
-/

namespace OeisA109227

open Nat List

/--
The primary defining sequence `a`.
$a(n)$ is the natural number whose decimal digits are given by the binary string of length $p_n$
where the $k$-th digit is $1$ if $k$ is prime and $0$ otherwise, with leading zeros dropped.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
  let prime_bits_full : List ℕ := (range (p_n + 1)).map (fun i =>
    if Nat.Prime i then 1 else 0
  )
  let prime_bits_trimmed := prime_bits_full.dropWhile (· = 0)
  ofDigits 10 prime_bits_trimmed.reverse

/--
Conjecture A109227 a(2) and a(121) are primes. Are there any more?
-/
@[category research open, AMS 11]
theorem main_conjecture :
    answer(sorry) ↔ ∃ n > 0, n ≠ 2 ∧ n ≠ 121 ∧ Nat.Prime (a n) := by
  sorry

end OeisA109227
