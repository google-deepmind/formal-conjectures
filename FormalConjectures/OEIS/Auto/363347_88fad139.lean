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

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


theorem a_three : A363347 3 = 11 := by
  sorry

theorem a_four : A363347 4 = 5 := by
  sorry

theorem a_five : A363347 5 = 31 := by
  sorry

theorem a_six : A363347 6 = 11 := by
  sorry

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  by sorry
