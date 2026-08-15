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
open Nat

/--
A001359 Lesser of twin primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n > 0 then
    (n - 1).nth (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
  else
    0


theorem a_one : a 1 = 3 := by
  norm_num[a]
  exact(((congr_arg _) (by constructor) )).trans.comp (3).nth_count (by decide)

theorem a_two : a 2 = 5 := by
  delta a
  apply((congr_arg _) (by constructor) ).trans (Nat.nth_count (by decide ) )

theorem a_three : a 3 = 11 := by
  (inhabit ℝ)
  norm_num[a]
  exact (congr_arg _ (by decide)).trans (Nat.nth_count (by decide))

theorem a_four : a 4 = 17 := by
  simp_all[a]
  exact (congr_arg _ (by constructor) ).trans (Nat.nth_count (by decide))


open Finset Nat.ModEq

/--
Conjecture: A001359 Primes `prime(k)` such that `prime(k)! == 1 (mod prime(k+1))` with the exception of
`prime(991) = 7841` and other unknown primes `prime(k)` for which
`(prime(k)+1)*(prime(k)+2)*...*(prime(k+1)-2) == 1 (mod prime(k+1))` where `prime(k+1) - prime(k) > 2`.
Here, `prime(k)` denotes the k-th prime number (1-indexed, so prime(k) = Nat.nth Nat.Prime (k-1) for k > 0).
-/
theorem oeis_1359_conjecture_6 :
  -- k is the 1-based index. We start with k > 1, corresponding to the first twin prime 3 (P_2).
  ∀ (k : ℕ), k > 1 →
  let Pk      := Nat.nth Nat.Prime (k - 1); -- Pk is the k-th prime
  let Pk_succ := Nat.nth Nat.Prime k;       -- Pk_succ is the (k+1)-th prime
  let Congruence := Nat.factorial Pk ≡ 1 [MOD Pk_succ];
  let IsLesserTwinPrime := Nat.Prime (Pk + 2);

  -- The product Wk_prod is $\prod_{i=P_k+1}^{P_{k+1}-2} i$. This defines the value W_k in the OEIS comment.
  let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;

  -- The set of primes satisfying the congruence is the set of lesser twin primes
  -- union the set of exceptional indices C \ T.
  Iff Congruence (
    IsLesserTwinPrime ∨
    (k = 991) ∨
    (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])
  )
:= by sorry
