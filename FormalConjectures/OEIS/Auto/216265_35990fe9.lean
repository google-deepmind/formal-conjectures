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

open Nat

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry
