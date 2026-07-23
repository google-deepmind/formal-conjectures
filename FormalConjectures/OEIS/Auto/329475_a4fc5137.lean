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

open Nat Int ZMod Finset

/--
The central trinomial coefficient $T(k) = A002426(k)$, which is the coefficient of $x^k$ in the expansion of $(x^2+x+1)^k$.
$$T(k) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i}$$
-/
def T (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => (n.choose k) * ((n - k).choose k)

/--
A329475: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 T(k) T(n-k)$, where $T(k) = A002426(k)$
is the coefficient of $x^k$ in the expansion of $(x^2+x+1)^k$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (n.choose k) ^ 2 * T k * T (n - k)

-- Sanity checks using sorry since proof is not the goal
theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 2 := by sorry
theorem a_two : a 2 = 10 := by sorry
theorem a_three : a 3 = 68 := by sorry

-- Helper definitions for the conjecture

/--
The sum $S = \sum_{k=0}^{p-1} a(k)/(-4)^k$ defined as an element of $\mathbb{Z} / p^2 \mathbb{Z}$.
-/
noncomputable def S_ZMod (p : ℕ) [Fact p.Prime] : ZMod (p^2) :=
  let R := ZMod (p^2)
  -- The inverse of -4 exists since p is an odd prime.
  let neg_4_inv : R := (-(4 : R))⁻¹
  Finset.sum (Finset.range p) fun k => (a k : R) * (neg_4_inv ^ k)

/--
The sum $S = \sum_{k=0}^{p-1} a(k)/(-4)^k$ as an integer representative in $\mathbb{Z}$,
obtained by taking the canonical natural number value of $S_{\mathbb{Z}/p^2\mathbb{Z}}$ and casting it to $\mathbb{Z}$.
-/
noncomputable def S (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) : ℤ :=
  (ZMod.val (S_ZMod p) : ℤ)

/--
Conjecture: Let p be an odd prime and let S = Sum_{k=0..p-1}a(k)/(-4)^k.
If p == 1 (mod 12) and p = x^2 + 9*y^2 with x and y integers, then  S == 4*x^2-2*p (mod p^2).
If p == 5 (mod 12) and p = x^2 + y^2 with x == y (mod 3), then S == 4*x*y (mod p^2).
If p == 3 (mod 4), then S == 0 (mod p^2).

Note: The congruence $x \equiv y \pmod 3$ is interpreted as $x \equiv y \pmod 3$ in $\mathbb{Z}$.
-/
theorem oeis_329475_conjecture_1_full {p : ℕ} (hp : Fact p.Prime) (h_odd : p ≠ 2) :
  (p % 12 = 1 → (∃ (x y : ℤ), (p : ℤ) = x^2 + 9 * y^2 ∧ S p h_odd ≡ 4 * x^2 - 2 * p [ZMOD p^2])) ∧
  (p % 12 = 5 → (∃ (x y : ℤ), (p : ℤ) = x^2 + y^2 ∧ x ≡ y [ZMOD 3] ∧ S p h_odd ≡ 4 * x * y [ZMOD p^2])) ∧
  (p % 4 = 3 → S p h_odd ≡ 0 [ZMOD p^2])
:= by sorry
