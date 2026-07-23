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
A320146: $a(n) = 2 \cdot \operatorname{prime}(n) \pmod{\operatorname{prime}(n-1) + \operatorname{prime}(n+1)}$.
$\operatorname{prime}(k)$ is the $k$-th prime number (1-indexed). The sequence is defined for $n \ge 2$.
We use Mathlib's $P(i) = \operatorname{Nat.nth} \operatorname{Nat.Prime} i$ (0-indexed prime).
The formula translates to:
$$a(n) = \left(2 \cdot P(n-1)\right) \bmod \left(P(n-2) + P(n)\right)$$
where subtraction $n-k$ is natural number subtraction.
-/
noncomputable def A320146 (n : ℕ) : ℕ :=
  let P i : ℕ := Nat.nth Nat.Prime i
  (2 * P (n - 1)) % (P (n - 2) + P n)

-- Helper definition for the 1-indexed prime function $\operatorname{prime}(n)$ used in the conjecture.
-- This corresponds to the $n$-th prime in OEIS's 1-indexed convention.
noncomputable def prime_oeis (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/--
oeis_320146_conjecture_0: Is $\lim_{n \to \infty} \left(\sum_{i=1}^n \operatorname{A320146}(i)\right) / \left(\sum_{i=1}^n \operatorname{prime}(i)\right)$ finite? If so, what is its value?
Since $\operatorname{A320146}(n)$ is only rigorously defined for $n \ge 2$, the sums are taken to start at $i=2$.
The conjecture is formalized as the existence of a limit in $\mathbb{R}$.
-/
theorem oeis_320146_conjecture_0 :
  -- We claim the sequence of ratios has a limit L in ℝ (which implies the limit is finite).
  ∃ L : ℝ, Filter.Tendsto
    (fun n : ℕ =>
      -- numerator: Sum_{i=2 to n} A320146(i) cast to ℝ
      (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ)))
      /
      -- denominator: Sum_{i=2 to n} prime(i) cast to ℝ
      (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))))
    Filter.atTop
    (nhds L) :=
by sorry
