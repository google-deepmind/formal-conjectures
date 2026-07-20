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

/-!
# Conjectures associated with A067720

A067720 lists numbers $k$ such that $\varphi(k^2 + 1) = k \cdot \varphi(k + 1)$,
where $\varphi$ is Euler's totient function.

The sequence exhibits a strong connection to primes: for almost all terms $k$,
$k + 1$ is prime. The conjecture states that $k = 8$ is the only exception.

*Reference:* [A67720](https://oeis.org/A67720)
-/

namespace OeisA67720

open Nat

/-- A number $k$ is in the sequence A067720 if $\varphi(k^2 + 1) = k \cdot \varphi(k + 1)$. -/
def A (k : ℕ) : Prop :=
  φ (k ^ 2 + 1) = k * φ (k + 1)

/-- $1$ is in the sequence A067720. -/
@[category test, AMS 11]
theorem a_1 : A 1 := by norm_num [A]

/-- $2$ is in the sequence A067720. -/
@[category test, AMS 11]
theorem a_2 : A 2 := by
  simp +decide only [A]

/-- $4$ is in the sequence A067720. -/
@[category test, AMS 11]
theorem a_4 : A 4 := by
  simp +decide only [A]

/-- $6$ is in the sequence A067720. -/
@[category test, AMS 11]
theorem a_6 : A 6 := by
  simp +decide only [A]

/-- $8$ is in the sequence A067720. -/
@[category test, AMS 11]
theorem a_8 : A 8 := by
  simp +decide only [A]

/-- $10$ is in the sequence A067720. -/
@[category test, AMS 11]
theorem a_10 : A 10 := by
  simp +decide only [A]

/-- If $k + 1$ and $k^2 + 1$ are both prime, then $k$ is in the sequence. -/
@[category textbook, AMS 11]
theorem a_of_primes {k : ℕ} (hk : (k + 1).Prime) (hk' : (k ^ 2 + 1).Prime) : A k := by
  rw [A, totient_prime hk', totient_prime hk, Nat.add_sub_cancel, Nat.add_sub_cancel, sq]

/-- For members of the sequence other than $8$, we have $k + 1$ is prime. -/
@[category research open, AMS 11]
theorem prime_add_one_of_a {k : ℕ} (h : A k) (hne : k ≠ 8) : (k + 1).Prime := by
  sorry

end OeisA67720
