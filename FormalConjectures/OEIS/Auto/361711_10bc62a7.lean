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

open Nat Int Finset BigOperators

/--
A361711: $a(1) = 1$ and $a(n) = \sum_{k = 0}^{n-2} (-1)^k \binom{n}{k}^2 \binom{n-2}{k}$ for $n \ge 2$.
-/
def A361711 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    -- $n-2$ is the upper limit of summation.
    let m : ℕ := N - 2

    -- The sum is over k from 0 to m, which is Finset.range (m + 1).
    (Finset.range (m + 1)).sum fun k : ℕ =>
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

/--
A361711 Conjecture: the supercongruence a(p^k) == a(p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and positive integer k.
-/
theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  sorry
