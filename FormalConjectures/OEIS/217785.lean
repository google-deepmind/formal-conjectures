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
# Smallest integer $s > n$ such that $1 + 2s + 3s^2 + \dots + n s^{n-1}$ is prime

For $n \ge 2$, $a(n)$ is the smallest integer $s > n$ such that the sum
$P_n(s) = \sum_{k=0}^{n-1} (k+1) s^k$ is a prime number.

*References:*
- [A217785](https://oeis.org/A217785)
-/

namespace OeisA217785

/-- `polyP n s` is the sum $\sum_{k=0}^{n-1} (k+1) s^k$. -/
def polyP (n s : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1) * s ^ k

open scoped Classical in
/-- `a n` is the smallest integer $s > n$ such that `polyP n s` is prime,
or `none` if no such $s$ exists. -/
noncomputable def a (n : ℕ) : Option ℕ :=
  if ∃ s : ℕ, n < s ∧ Nat.Prime (polyP n s) then
    some (sInf {s : ℕ | n < s ∧ Nat.Prime (polyP n s)})
  else
    none

/-- `polyS n` is the polynomial $s_n(x) = \sum_{k=0}^n (k+1) x^k$ over $\mathbb{Z}[x]$. -/
noncomputable def polyS (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (k + 1 : ℤ) * Polynomial.X ^ k

@[category test, AMS 11]
theorem a_2 : a 2 = some 3 := by
  have h : IsLeast {s : ℕ | 2 < s ∧ Nat.Prime (polyP 2 s)} 3 := by
    refine ⟨by norm_num [polyP], fun x hx => ?_⟩
    by_contra! h
    interval_cases x <;> norm_num [polyP] at hx
  have h_ex : ∃ s : ℕ, 2 < s ∧ Nat.Prime (polyP 2 s) := ⟨3, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

@[category test, AMS 11]
theorem a_3 : a 3 = some 12 := by
  have h : IsLeast {s : ℕ | 3 < s ∧ Nat.Prime (polyP 3 s)} 12 := by
    refine ⟨by norm_num [polyP], fun x hx => ?_⟩
    by_contra! h
    interval_cases x <;> norm_num [polyP] at hx
  have h_ex : ∃ s : ℕ, 3 < s ∧ Nat.Prime (polyP 3 s) := ⟨12, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

@[category test, AMS 11]
theorem a_4 : a 4 = some 12 := by
  have h : IsLeast {s : ℕ | 4 < s ∧ Nat.Prime (polyP 4 s)} 12 := by
    refine ⟨by norm_num [polyP], fun x hx => ?_⟩
    by_contra! h
    interval_cases x <;> norm_num [polyP] at hx
  have h_ex : ∃ s : ℕ, 4 < s ∧ Nat.Prime (polyP 4 s) := ⟨12, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

@[category test, AMS 11]
theorem a_5 : a 5 = some 9 := by
  have h : IsLeast {s : ℕ | 5 < s ∧ Nat.Prime (polyP 5 s)} 9 := by
    refine ⟨by norm_num [polyP], fun x hx => ?_⟩
    by_contra! h
    interval_cases x <;> norm_num [polyP] at hx
  have h_ex : ∃ s : ℕ, 5 < s ∧ Nat.Prime (polyP 5 s) := ⟨9, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

@[category test, AMS 11]
theorem a_6 : a 6 = some 21 := by
  have h : IsLeast {s : ℕ | 6 < s ∧ Nat.Prime (polyP 6 s)} 21 := by
    refine ⟨by norm_num [polyP], fun x hx => ?_⟩
    by_contra! h
    interval_cases x <;> norm_num [polyP] at hx
  have h_ex : ∃ s : ℕ, 6 < s ∧ Nat.Prime (polyP 6 s) := ⟨21, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

/--
Conjecture: For each $n \ge 2$, there are infinitely many primes of the form
$1 + 2s + \dots + n s^{n-1}$ where $s$ is a positive integer.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 ≤ n) :
    {s : ℕ | 0 < s ∧ Nat.Prime (polyP n s)}.Infinite := by
  sorry

/--
Conjecture: For each $n \ge 2$, $a(n) < 12 n^2$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 2 ≤ n) :
    ∃ m < 12 * n ^ 2, a n = some m := by
  sorry

/--
Conjecture: The polynomials $s_n(x) = \sum_{k=0}^n (k+1) x^k$ for
$n \ge 1$ are all irreducible over the field of rational numbers; moreover, $s_n(x)$ is
reducible modulo every prime if and only if $n$ has the form $8k(k+1)$ where $k$ is a
positive integer.
-/
@[category research open, AMS 11 12]
theorem conjecture3 (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (polyS n)) ∧
      ((∀ p : ℕ, p.Prime → ¬ Irreducible (Polynomial.map (Int.castRingHom (ZMod p)) (polyS n))) ↔
        ∃ k : ℕ, 0 < k ∧ n = 8 * k * (k + 1)) := by
  sorry

end OeisA217785
