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
module

public import FormalConjecturesUtil

/-!
# Numbers $n$ such that $\phi(n) = \phi(n + \phi(n))$

*References:*
- [A108569](https://oeis.org/A108569)

The conjecture of Farideh Firoozbakht (2005) that all terms except the first are even is false.
The odd number $5095354107 = 3 \cdot 1033 \cdot 1644193$ is a term of the sequence;
another odd term is $855110560461$.
-/

@[expose] public section

namespace OeisA108569

open scoped Nat

/-- The predicate defining whether $k$ belongs to the sequence. -/
def A (k : ℕ) : Prop := 0 < k ∧ φ k = φ (k + φ k)

instance : DecidablePred A := by
  unfold A
  infer_instance

/--
The primary defining sequence `a`.
`a n` is the $(n+1)$-th positive integer $k$ such that $\phi(k) = \phi(k + \phi(k))$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h1 : A 1 := by decide
  have hcnt : Nat.count A 1 = 0 := by decide
  have := Nat.nth_count (p := A) h1
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by
  have h4 : A 4 := by decide
  have hcnt : Nat.count A 4 = 1 := by decide
  have := Nat.nth_count (p := A) h4
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_2 : a 2 = 8 := by
  have h8 : A 8 := by decide
  have hcnt : Nat.count A 8 = 2 := by decide
  have := Nat.nth_count (p := A) h8
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_3 : a 3 = 16 := by
  have h16 : A 16 := by decide
  have hcnt : Nat.count A 16 = 3 := by decide
  have := Nat.nth_count (p := A) h16
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_4 : a 4 = 32 := by
  have h32 : A 32 := by decide
  have hcnt : Nat.count A 32 = 4 := by decide
  have := Nat.nth_count (p := A) h32
  rwa [hcnt] at this

/-- The odd number $5095354107 = 3 \cdot 1033 \cdot 1644193$ is in the sequence:
$\phi(5095354107) = 3393612288 = \phi(8488966395)$, where
$8488966395 = 5095354107 + \phi(5095354107) = 3 \cdot 5 \cdot 7 \cdot 13 \cdot 19 \cdot 327317$. -/
@[category test, AMS 11]
theorem A_5095354107 : A 5095354107 := by
  have h₁ : φ 5095354107 = 3393612288 := by
    rw [show 5095354107 = 3 * 1033 * 1644193 by norm_num,
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]
  have h₂ : φ 8488966395 = 3393612288 := by
    rw [show 8488966395 = 3 * 5 * 7 * 13 * 19 * 327317 by norm_num,
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  refine ⟨by norm_num, ?_⟩
  rw [h₁, show 5095354107 + 3393612288 = 8488966395 by norm_num, h₂]

/-- A second odd term, not a multiple of the first: $855110560461 = 3 \cdot 1297 \cdot 6053 \cdot 36307$.
Here $\phi(855110560461) = 569524379904 = \phi(1424634940365)$, where
$1424634940365 = 3 \cdot 5 \cdot 7 \cdot 13 \cdot 19 \cdot 54930979$. -/
@[category test, AMS 11]
theorem A_855110560461 : A 855110560461 := by
  have h₁ : φ 855110560461 = 569524379904 := by
    rw [show 855110560461 = 3 * 1297 * 6053 * 36307 by norm_num,
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  have h₂ : φ 1424634940365 = 569524379904 := by
    rw [show 1424634940365 = 3 * 5 * 7 * 13 * 19 * 54930979 by norm_num,
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  refine ⟨by norm_num, ?_⟩
  rw [h₁, show 855110560461 + 569524379904 = 1424634940365 by norm_num, h₂]

/--
Farideh Firoozbakht conjectured that all terms of A108569 except the first one ($a_0 = 1$) are
even. This is false: $5095354107$ is an odd term (see `A_5095354107`).
-/
@[category research solved, AMS 11]
theorem conjecture : ¬ ∀ n, 0 < n → Even (a n) := by
  intro h
  have hpos : 0 < Nat.count A 5095354107 := by
    have h₁ : Nat.count A 5 = 2 := by decide
    have h₂ := Nat.count_monotone A (show 5 ≤ 5095354107 by norm_num)
    omega
  have := h _ hpos
  rw [a, Nat.nth_count A_5095354107] at this
  revert this
  decide

end OeisA108569
