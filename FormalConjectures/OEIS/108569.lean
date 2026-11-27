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

/-- There is an odd term $n>1$ coprime to $3$ for which exactly seven distinct primes
divide $n$ or $n+\varphi(n)$. The witness is $1162699874939$. -/
@[category test, AMS 11]
theorem exists_odd_term_seven_prime_factors :
    ∃ n > 1, Odd n ∧ n.Coprime 3 ∧ A n ∧
      (n.primeFactors ∪ (n + φ n).primeFactors).card = 7 := by
  have hn : (1162699874939 : ℕ) = 257 * 7253 * 623759 := by decide
  have hφ : φ 1162699874939 = 1158014212096 := by
    rw [hn]
    simp (disch := norm_num1) only [Nat.totient_mul, Nat.totient_prime]
  have hm : 1162699874939 + φ 1162699874939 = 3 * 5 * 17 * 173 * 7253 ^ 2 := by
    rw [hφ]
    decide
  refine ⟨1162699874939, by decide, by decide, by decide, ⟨by decide, ?_⟩, ?_⟩
  · rw [hm, hφ]
    simp (disch := norm_num1) only [Nat.totient_mul, Nat.totient_prime_pow_succ, Nat.totient_prime]
    decide
  · rw [hm, hn]
    simp (disch := norm_num1) only [Nat.primeFactors_mul, Nat.primeFactors_pow,
      Nat.Prime.primeFactors]
    decide

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

/-- Conjecture: Except for the first term all terms are even. -/
@[category research open, AMS 11]
theorem conjecture : ∀ n, 0 < n → Even (a n) := by
  sorry

end OeisA108569
