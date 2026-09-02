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
open PNat

/--
A078680: Smallest $m > 0$ such that $n \cdot 2^m + 1$ is prime, or $0$ if no such $m$ exists.
We search for the smallest element in the set of positive natural numbers ($\mathbb{N}^+$ or PNat) satisfying the primality condition.
-/
noncomputable def A078680 (n : ℕ) : ℕ :=
  -- Predicate P on PNat: n * 2^m + 1 is prime.
  let P (m : PNat) : Prop := Nat.Prime (n * 2 ^ (m : ℕ) + 1)

  -- Use classical logic to determine if a solution exists.
  match Classical.dec (∃ m : PNat, P m) with
  | isTrue h_exist => (PNat.find h_exist).val -- Find the smallest PNat m, and convert to Nat.
  | isFalse _      => 0                       -- Return 0 if no such PNat exists.


theorem a_one : A078680 1 = 1 := by sorry

theorem a_two : A078680 2 = 1 := by sorry

theorem a_three : A078680 3 = 1 := by sorry

theorem a_four : A078680 4 = 2 := by sorry

open Nat

/--
Conjecture from OEIS A078680:
The claim that the first $n > 0$ for which $A078680(n)=0$ is $n=65536$ is equivalent to
the statement that all Fermat numbers $F_k = 2^{2^k} + 1$ for $k > 4$ are composite.

Here, $65536 = 2^{16}$.
-/
theorem oeis_A078680_conjecture_equivalence :
  (A078680 (2^16) = 0 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))
  ↔
  (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  sorry
