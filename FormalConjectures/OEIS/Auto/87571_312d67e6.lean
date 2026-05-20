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
A087571: Smallest prime which has the form of the concatenation $n, n-1, n-2, n-3, \dots, n-k$ for some $k < n$, or 0 if no such prime exists.
-/
noncomputable def a (n : ℕ) : ℕ :=

  -- Helper function to get the concatenated digits of a list of numbers in MSD-first order.
  let get_all_digits_msf (L : List ℕ) : List ℕ :=
    let to_digits_msb (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse
    -- Concatenates the list of digit lists using foldr, equivalent to List.join (List.map to_digits_msb L).
    List.foldr (fun num acc_digits => (to_digits_msb num) ++ acc_digits) [] L

  -- Helper function to convert a list of digits (MSF) to a number.
  let of_msb_digits (D : List ℕ) : ℕ :=
    D.foldl (fun acc d => acc * 10 + d) 0

  -- The core concatenation logic: n || (n-1) || ... || (n-k)
  let concatenated_number (k : ℕ) : ℕ :=
    -- The list of numbers is `[n, n-1, ..., n-k]`. We ensure subtraction is safe for `i < n`.
    let num_list : List ℕ := List.map (fun i => n - i) (List.range (k + 1))
    of_msb_digits (get_all_digits_msf num_list)

  -- The possible values for k are 0 up to n-1.
  -- List.range n generates [0, 1, ..., n-1].
  let candidates : List ℕ :=
    List.map concatenated_number (List.range n)

  -- Find the smallest prime.
  match List.find? Nat.Prime candidates with
  | some p => p
  | none   => 0

/-- Conjecture; There are infinitely many composite numbers n such that a(n) is nonzero. -/
theorem oeis_a087571_conjecture :
  -- The set of N such that N > 1 and N is composite and a(N) != 0 is infinite.
  ∀ M : ℕ, ∃ n : ℕ, n > M ∧ (n > 1 ∧ ¬ Nat.Prime n) ∧ a n ≠ 0 := by
  sorry
