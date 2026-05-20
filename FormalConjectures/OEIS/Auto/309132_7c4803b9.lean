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

open Rat Nat

/--
A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    F_n.den

/-- Definition of a Carmichael number $n$: a composite number s.t. $b^{n-1} \equiv 1 \pmod n$ for all $b$ coprime to $n$. -/
def is_carmichael_number (n : ℕ) : Prop :=
  (¬ Nat.Prime n ∧ n > 1) ∧ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n])

/-- Helper definition for "composite number" -/
def is_composite (n : ℕ) : Prop := ¬ Nat.Prime n ∧ n > 1

/--
OEIS A309132 Conjecture: composite numbers n such that a(n) is squarefree are only the Carmichael numbers A002997.
-/
theorem A309132_conjecture_carmichael : ∀ (n : ℕ),
  (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n :=
by sorry
