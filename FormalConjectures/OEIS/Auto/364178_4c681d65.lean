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

open Real
open Nat

/--
A364178: The conjecturally integral sequence
$$a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$$
where $x! := \Gamma(x+1)$ for real $x$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (round
    ((Gamma (10 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) + 1) * Gamma ((↑n : ℝ) / 2 + 1)) /
     (Gamma (6 * (↑n : ℝ) + 1) * Gamma (5 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) / 2 + 1) * Gamma (↑n + 1)))
  ).toNat


/-- A364178 Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r. -/
theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
by sorry
