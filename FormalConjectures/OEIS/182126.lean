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

/-!
# Product of two consecutive primes modulo the next prime

The sequence is defined by
$$a(n) = \mathrm{prime}(n) \cdot \mathrm{prime}(n+1) \bmod \mathrm{prime}(n+2),$$
where $\mathrm{prime}(k)$ is the $k$-th prime number ($\mathrm{prime}(1)=2$).

*References:*
- [A182126](https://oeis.org/A182126)-/

namespace OeisA182126

/-- $\mathrm{prime}(k)$ is the $k$-th prime number ($\mathrm{prime}(1) = 2$). -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- $a(n) = \mathrm{prime}(n) \cdot \mathrm{prime}(n+1) \bmod \mathrm{prime}(n+2)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (prime n * prime (n + 1)) % prime (n + 2)

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := (2).nth_count (by decide : (2).Prime)
  have h1 : Nat.nth Nat.Prime 1 = 3 := (3).nth_count (by decide : (3).Prime)
  have h2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  show (Nat.nth Nat.Prime 0 * Nat.nth Nat.Prime 1) % Nat.nth Nat.Prime 2 = 1
  rw [h0, h1, h2]

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have h1 : Nat.nth Nat.Prime 1 = 3 := (3).nth_count (by decide : (3).Prime)
  have h2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  have h3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  show (Nat.nth Nat.Prime 1 * Nat.nth Nat.Prime 2) % Nat.nth Nat.Prime 3 = 1
  rw [h1, h2, h3]

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  have h2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  have h3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  have h4 : Nat.nth Nat.Prime 4 = 11 := (11).nth_count (by decide : (11).Prime)
  show (Nat.nth Nat.Prime 2 * Nat.nth Nat.Prime 3) % Nat.nth Nat.Prime 4 = 2
  rw [h2, h3, h4]

@[category test, AMS 11]
theorem a_4 : a 4 = 12 := by
  have h3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  have h4 : Nat.nth Nat.Prime 4 = 11 := (11).nth_count (by decide : (11).Prime)
  have h5 : Nat.nth Nat.Prime 5 = 13 := (13).nth_count (by decide : (13).Prime)
  show (Nat.nth Nat.Prime 3 * Nat.nth Nat.Prime 4) % Nat.nth Nat.Prime 5 = 12
  rw [h3, h4, h5]

/-- Count of occurrences of value $v$ among $a(1), \dots, a(x)$. -/
noncomputable def countA (x v : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/-- $v_0$ is a most frequent value among $a(1), \dots, a(x)$. -/
def IsMostFrequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, countA x v ≤ countA x v₀

/--
Conjecture: For $x > 10^9$, the most frequent value in $a(n)$, $n=1\dots x$, has form $120k$.
-/
@[category research open, AMS 11]
theorem conjecture1 (x : ℕ) (hx : 10 ^ 9 < x) (v₀ : ℕ) (hv : IsMostFrequent x v₀) :
    120 ∣ v₀ := by
  sorry

/--
Let $b = \mathrm{prime}(n+2) - \mathrm{prime}(n)$ and $c = \mathrm{prime}(n+2) - \mathrm{prime}(n+1)$.
Conjecture: for $n > 61$, $a(n) = b \cdot c$.
- _Charles R Greathouse IV_, May 11 2012
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 61 < n) :
    let b := prime (n + 2) - prime n
    let c := prime (n + 2) - prime (n + 1)
    a n = b * c := by
  sorry

/--
Are 2, 7, 11, 13, 29 the only primes in this sequence?
- _Hugo Pfoertner_, Sep 22 2025
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 0 < n) :
    (a n).Prime ↔ a n ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  sorry

end OeisA182126
