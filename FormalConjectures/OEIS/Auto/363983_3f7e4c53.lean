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

open Nat Finset Int

/--
A363983: The sequence defined by
$$a(n) = \sum_{k = \lfloor\frac{n+1}{2}\rfloor}^n (-1)^{n+k} \binom{n}{k} \binom{n+k-1}{k} \binom{2k}{n}$$
The sum is implemented over $k=0$ to $n$ in $\mathbb{Z}$ and then cast to $\mathbb{N}$, as the sequence is known to be non-negative.
Note: The sum limits in the OEIS sequence definition are $\lfloor(n+1)/2\rfloor \le k \le n$. The definition below, summing $k=0$ to $n$, is equivalent because $\binom{2k}{n}=0$ for $2k < n$, i.e. $k < n/2$. The term $\binom{n+k-1}{k}$ is zero for $k < 0$ (vacuously true here) or when $n+k-1 < k$ and $k \ne 0$, i.e., $n-1 < 0$, or $n=0$ and $k>0$. For $n=0$, the only term is $k=0 \Rightarrow 1$. For $n>0$, $n+k-1 \ge k$ holds for non-negative $k$, and all terms for $k < \lceil n/2 \rceil$ are correct either way. Given the OEIS formula simplifies to the $k=0$ to $n$ sum via the identity shown in the comments, this definition is a standard equivalent form.
-/
def A363983 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k : ℕ =>
    -- The expression must result in ℤ due to the alternating sign.
    let sign_factor : ℤ := (-1) ^ (n + k)
    -- Binomial coefficients (Nat.choose) are implicitly coerced to ℤ for multiplication.
    -- (n + k - 1).choose k is written as ((n + k).pred.choose k) in Mathlib's Nat.choose syntax.
    let term_val : ℤ := (n.choose k) * ((n + k).pred.choose k) * ((2 * k).choose n)
    sign_factor * term_val
  ).toNat

/-- oeis_363983_conjecture_0: The Franel numbers satisfy the supercongruences A000172(n*p^r) == A000172(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r. We conjecture that the present sequence satisfies the same supercongruences. -/
theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry
