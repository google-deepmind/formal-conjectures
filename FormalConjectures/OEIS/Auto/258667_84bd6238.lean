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

open BigOperators Nat Int Real Asymptotics Filter

/--
The inner sum of the formula used in A258667:
$$\sum_{\max(k-n+5, 0) \le j \le \min(k,4)} \binom{8-j}{j}\binom{2n-k+j-10}{k-j}$$
-/
private def A258667_inner_sum (n k : ℕ) : ℤ :=
  let L : ℕ := max 0 (k + 5 - n)
  let U : ℕ := min k 4
  Finset.sum (Finset.Icc L U) fun j =>
    let term1 := Nat.choose (8 - j) j
    -- The top argument of the second binomial coefficient is written in Nat subtraction form.
    let term2 := Nat.choose (2 * n + j - (k + 10)) (k - j)
    ofNat term1 * ofNat term2

/--
A258667: A total of $n$ married couples, including a mathematician M and his wife, are to be seated at the $2n$ chairs around a circular table, with no man seated next to his wife. After the ladies are seated at every other chair, M is the first man allowed to choose one of the remaining chairs. The sequence gives the number of ways of seating the other men, with no man seated next to his wife, if M chooses the chair that is 9 seats clockwise from his wife's chair.

$$a(n) = \begin{cases} 0 & \text{if } n \le 5 \\ \sum_{k=0}^{n-1}(-1)^k(n-k-1)! \sum_{\max(k-n+5, 0) \le j \le \min(k,4)} \binom{8-j}{j}\binom{2n-k+j-10}{k-j} & \text{if } n > 5 \end{cases}$$
-/
def A258667 (n : ℕ) : ℕ :=
  if h : n ≤ 5 then 0 else
  (Finset.sum (Finset.range n) fun k =>
    let sign : ℤ := if k % 2 = 0 then 1 else -1
    -- Nat.factorial (n - 1 - k) is safe since h implies n > 5 and k < n.
    let fac_term : ℤ := ofNat (Nat.factorial (n - 1 - k))

    sign * fac_term * A258667_inner_sum n k
  ).natAbs


theorem a_one : A258667 1 = 0 := by
  rfl

theorem a_two : A258667 2 = 0 := by
  rfl

theorem a_three : A258667 3 = 0 := by
  rfl

theorem a_four : A258667 4 = 0 := by
  rfl

-- Start of formalization of the conjecture

noncomputable def nat_fac_to_real (n : ℕ) : ℝ := (Nat.factorial n : ℝ)

/-- The denominator term $k! (n-1)_k$ represented as a Real number. -/
noncomputable def menage_denom_term (n k : ℕ) : ℝ :=
  let k_fac_R := nat_fac_to_real k
  -- (n-1)_k is the falling factorial. Nat.descFactorial (n-1) k is (n-1)!/(n-1-k)!
  let falling_fac := (Nat.descFactorial (n - 1) k : ℝ)
  k_fac_R * falling_fac

/-- The infinite series part of the asymptotic expansion: $\sum_{k \ge 1} \frac{(-1)^k}{k!(n-1)_k}$. -/
noncomputable def A258667_asymptotic_sum_part (n : ℕ) : ℝ :=
  -- The sum is effectively finite since (n-1)_k is 0 for k >= n.
  Finset.sum (Finset.range n) fun k =>
    if k = 0 then 0
    else
      let denom := menage_denom_term n k
      -- Denominator is non-zero if n >= 1 and 1 <= k < n.
      if denom = 0 then 0
      else ((-1 : ℝ) ^ k) / denom

/-- The proposed asymptotic expression for A258667(n). -/
noncomputable def A258667_asymptotic_term (n : ℕ) : ℝ :=
  if n ≤ 2 then 0 -- Avoid division by zero, irrelevant for n -> infinity
  else
    let n_R : ℝ := n
    let n_fac_R := nat_fac_to_real n
    let prefactor : ℝ := exp (-2) * (n_fac_R / (n_R - 2))
    prefactor * (1 + A258667_asymptotic_sum_part n)

/--
A258667 Conjecture:
Therefore, it is natural to conjecture that a(n) ~ e^(-2)*n!/(n-2)*(1 + Sum_{k>=1} (-1)^k/(k!(n-1)_k)).
-/
theorem oeis_A258667_conjecture_0 :
  IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) A258667_asymptotic_term := by
  sorry
