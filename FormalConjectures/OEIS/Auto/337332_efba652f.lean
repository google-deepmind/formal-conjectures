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

open Finset Nat Int ZMod

/--
A337332: $a(n) = \sum_{k=0}^n \binom{n}{k}\binom{n+k}{k}\binom{2k}{k}\binom{2n-2k}{n-k}(-8)^{n-k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    -- Nat.centralBinom m = (2 * m).choose m which is C(2(n-k), n-k)
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)


theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = -12 := by sorry
theorem a_two : a 2 = 228 := by sorry
theorem a_three : a 3 = -3504 := by sorry


/--
Conjecture 4 from A337332:
Let $p > 3$ be a prime, and let $S(p) = \sum_{k=0}^{p-1} a(k)/(-48)^k$.
If $p \equiv 1 \pmod 4$ and $p = x^2 + 4y^2$ with $x$ and $y$ integers, then $S(p) \equiv 4x^2-2p \pmod{p^2}$.
If $p \equiv 3 \pmod 4$, then S(p) $\equiv 0 \pmod{p^2}$.
-/
theorem oeis_337332_conjecture_4 (p : ℕ) (hp : Nat.Prime p) (hp_gt_3 : p > 3) :
    let P_sq : ℕ := p ^ 2
    let R : Type := ZMod P_sq

    -- Define the inverse of -48 in ZMod p^2. It exists since p > 3, so 48 is coprime to p^2.
    let neg_48_inv_zmod : R := ((-48 : ℤ) : R)⁻¹

    let S_p : R := Finset.sum (range p) fun k =>
      (a k : R) * (neg_48_inv_zmod ^ k)

    (p % 4 = 1 →
      ∃ (x y : ℤ),
        (p : ℤ) = x ^ 2 + 4 * y ^ 2 ∧ S_p = ((4 * x ^ 2 - 2 * p : ℤ) : R)
    ) ∧
    (p % 4 = 3 → S_p = 0) :=
by sorry
