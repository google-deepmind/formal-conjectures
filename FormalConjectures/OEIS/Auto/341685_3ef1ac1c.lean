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

open Nat BigOperators

/--
The $p$-adic numbers `Padic p` require `p` to be a prime.
We assert this fact for $p=3$.
-/
instance : Fact (Nat.Prime 3) := by
  constructor
  norm_num

/--
The $m$-th successive approximation of the 3-adic integer $\sum_{k \ge 0} k!$.
This is $X_m = \left(\sum_{k=0}^\infty k!\right) \bmod 3^m$, computed here using a truncated sum since $\nu_3(k!)$ grows quickly.
We use a safe upper bound of $3m-1$ for the summation.
-/
def approx_3_adic_sum_factorial (m : ℕ) : ℕ :=
  let p := 3
  if m = 0 then 0
  else
    -- The upper limit for the sum is $p \cdot m$.
    let upper_k := p * m
    (Finset.range upper_k).sum Nat.factorial % (p ^ m)

/--
A341685: Expansion of the 3-adic integer $\sum_{k\ge 0} k!$.
The $n$-th digit $a(n)$ is the coefficient of $3^n$.
$$a(n) = \frac{\left(\sum_{k=0}^\infty k!\right) \bmod 3^{n+1} - \left(\sum_{k=0}^\infty k!\right) \bmod 3^n}{3^n}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p := 3
  let X_n_plus_1 := approx_3_adic_sum_factorial (n + 1)
  let X_n := approx_3_adic_sum_factorial n

  -- The subtraction is safe because $X_{n+1} \ge X_n$.
  (X_n_plus_1 - X_n) / (p ^ n)

theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 0 := by sorry
theorem a_two : a 2 = 1 := by sorry
theorem a_three : a 3 = 2 := by sorry

/--
The 3-adic constant $\xi_3 = \sum_{k \ge 0} k!$.
This series converges in `Padic 3`.
-/
noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

open Algebra

/--
Conjecture: this constant is transcendental, which means that it is not the root of any polynomial with integer coefficients.

Formally, $\xi_3$ is not algebraic over $\mathbb{Q}$.
-/
theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  sorry
