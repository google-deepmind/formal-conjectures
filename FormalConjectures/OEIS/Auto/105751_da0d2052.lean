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

open Complex Filter Asymptotics Topology

/--
A105751: Imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, where $i = \sqrt{-1}$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)

-- Formalized as 'by sorry' as proofs are not required.
theorem a_zero : a 0 = 0 := by sorry
theorem a_one : a 1 = 1 := by sorry
theorem a_two : a 2 = 3 := by sorry
theorem a_three : a 3 = 0 := by sorry

open Nat

/--
Conjecture (Moll's Conjecture 5.5 analogue for A105751, Type 1 primes):
The set of Type 1 primes is empty; that is, every prime $p$ divides some term of this sequence.
More formally, for every prime $p$, there exists an $n$ such that $p$ (as an integer) divides $a(n)$.
-/
theorem oeis_A105751_conjecture_Type_1_empty (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, (p : ℤ) ∣ a n := by
  sorry

section AsymptoticConjectures

-- We use the definition of $f(n) \sim g(n)$ as $\lim_{n \to \infty} \frac{f(n)}{g(n)} = 1$.

/--
Conjecture (Moll's Conjecture 5.5 analogue for A105751, Type 2 prime p=2):
The 2-adic valuation $v_2(a(n))$ has asymptotic linear behavior,
specifically, $v_2(a(n)) \sim n/4$ as $n \to \infty$.
-/
theorem oeis_A105751_conjecture_Moll_2 :
    Tendsto (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (nhds 1) := by
  -- This is equivalent to $\lim_{n \to \infty} \frac{v_2(a(n))}{n/4} = 1$.
  sorry

/--
Conjecture (Moll's Conjecture 5.5 analogue for A105751, Type 2 primes $p \equiv 1 \pmod 4$):
For primes $p \equiv 1 \pmod 4$ (rational primes that split in $\mathbb{Q}[i]$),
the $p$-adic valuation $v_p(a(n))$ has asymptotic linear behavior,
specifically, $v_p(a(n)) \sim n/(p-1)$ as $n \to \infty$.
-/
theorem oeis_A105751_conjecture_Moll_p_mod_4_eq_1 {p : ℕ} (hp : p.Prime) (h_mod : p % 4 = 1) :
    Tendsto (fun n ↦ ((p - 1 : ℚ) * (padicValInt p (a n) : ℚ)) / (n : ℚ)) atTop (nhds 1) := by
  -- This is equivalent to $\lim_{n \to \infty} \frac{v_p(a(n))}{n/(p-1)} = 1$.
  -- Note: $p > 0$, so $p-1 > 0$.
  sorry

end AsymptoticConjectures
