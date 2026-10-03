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
# Least $m > 0$ such that $\{2^k - k : k = 1, \dots, m\}$ covers all residues modulo $n$

*References:*
- [A232616](https://oeis.org/A232616)
-/

namespace OeisA232616

/--
The predicate that $\{2^k - k : k = 1, \dots, m\}$ contains a complete system
of residues modulo $n$.
-/
def HasCompleteResidueSystem (n m : ℕ) [NeZero n] : Prop :=
  (Finset.univ : Finset (ZMod n)) =
    (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

instance (n m : ℕ) [NeZero n] : Decidable (HasCompleteResidueSystem n m) :=
  decEq _ _

@[category API, AMS 11]
lemma isLeast_hasCompleteResidueSystem {n k : ℕ} [NeZero n]
    (hk : HasCompleteResidueSystem n k)
    (hmin : ∀ m < k, ¬ HasCompleteResidueSystem n m) :
    IsLeast {m | HasCompleteResidueSystem n m} k :=
  ⟨hk, fun m hm => not_lt.mp (fun hlt => hmin m hlt hm)⟩

open Classical in
/--
The primary defining sequence `a`.
$a(n)$ is the least positive integer $m$ such that $\{2^k - k : k = 1, \dots, m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have : NeZero n := NeZero.mk h
    sInf { m : ℕ | HasCompleteResidueSystem n m }

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [a, dif_neg (by decide)]
  exact (isLeast_hasCompleteResidueSystem (by decide) (by decide)).csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  rw [a, dif_neg (by decide)]
  exact (isLeast_hasCompleteResidueSystem (by decide) (by decide)).csInf_eq

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  rw [a, dif_neg (by decide)]
  exact (isLeast_hasCompleteResidueSystem (by decide) (by decide)).csInf_eq

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  rw [a, dif_neg (by decide)]
  exact (isLeast_hasCompleteResidueSystem (by decide) (by decide)).csInf_eq

@[category test, AMS 11]
theorem a_5 : a 5 = 10 := by
  rw [a, dif_neg (by decide)]
  exact (isLeast_hasCompleteResidueSystem (by decide) (by decide)).csInf_eq

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).

Disproved by Adamczewski for $n = 550172$.
-/
@[category research solved, AMS 11]
theorem conjecture1 : ∀ n > 0, a n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

/--
Conjecture (ii): The Diophantine equation $x^n - n = y^m$ with $m, n, x, y > 1$ only has
two integral solutions: $2^5 - 5 = 3^3$ and $2^7 - 7 = 11^2$. Also, the Diophantine equation
$x^n + n = y^m$ with $m, n, x, y > 1$ only has two integral solutions: $5^2 + 2 = 3^3$
and $5^3 + 3 = 2^7$.
-/
@[category research open, AMS 11]
theorem conjecture2 :
    (∀ x y n m : ℕ, 1 < x → 1 < y → 1 < n → 1 < m →
      x ^ n - n = y ^ m ↔ (x = 2 ∧ n = 5 ∧ y = 3 ∧ m = 3) ∨ (x = 2 ∧ n = 7 ∧ y = 11 ∧ m = 2)) ∧
    (∀ x y n m : ℕ, 1 < x → 1 < y → 1 < n → 1 < m →
      x ^ n + n = y ^ m ↔ (x = 5 ∧ n = 2 ∧ y = 3 ∧ m = 3) ∨ (x = 5 ∧ n = 3 ∧ y = 2 ∧ m = 7)) := by
  sorry

end OeisA232616
