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

import FormalConjecturesUtil
import FormalConjectures.OEIS.«3625»

/-!
# $a(n) = \sum_{k=0}^n \binom{2k}{k}^3$

The sequence $a(n) = 1 + \binom{2}{1}^3 + \binom{4}{2}^3 + \cdots + \binom{2n}{n}^3$:
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^3$$

*References:*
- [A079727](https://oeis.org/A079727)-/

namespace OeisA79727

/-- $a(n) = \sum_{k=0}^n \binom{2k}{k}^3$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * k) k) ^ 3

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 9 := by
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 225 := by
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 8225 := by
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 351225 := by
  rfl

/--
Conjecture 1 (Peter Bala, 2024):
If prime $p$ is in A003625 then $a(p^2) \equiv 8 + p^2 \pmod{p^3}$.
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : OeisA3625.A p) :
    a (p ^ 2) ≡ 8 + p ^ 2 [MOD p ^ 3] := by
  sorry

/--
Conjecture 2 (Peter Bala, 2024):
If prime $p$ is in A003625 then $a(p(p-1)) \equiv p^2 \pmod{p^3}$.
-/
@[category research open, AMS 11]
theorem conjecture2 (p : ℕ) (hp : OeisA3625.A p) :
    a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  sorry

/--
Conjecture 3 (Peter Bala, 2024):
If prime $p$ is in A003625 then $a((p^2-1)/2) \equiv p^2 \pmod{p^4}$.
-/
@[category research open, AMS 11]
theorem conjecture3 (p : ℕ) (hp : OeisA3625.A p) :
    a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 4] := by
  sorry

/--
Conjecture 4 (Peter Bala, 2024):
If $n$ is a product of distinct primes from A003625 then $a((n-1)/2)$ is divisible by $n^2$.
-/
@[category research open, AMS 11]
theorem conjecture4 (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ a ((∏ p ∈ S, p - 1) / 2) := by
  sorry

end OeisA79727

