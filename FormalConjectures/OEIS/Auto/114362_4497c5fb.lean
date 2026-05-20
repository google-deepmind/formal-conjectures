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

open scoped Nat

open Filter Asymptotics

/--
A114362: Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).

The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.
-/
noncomputable def A114362 (n : ℕ) : ℕ :=
  if h : n = 0 then
    2
  else
    -- Bernoulli numbers B_k are rational numbers.
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    -- Binomial coefficient $\binom{4n}{2n}$ as a rational number.
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))

    -- The rational quantity Q_n = -2 * B_4n / (B_2n^2 * \binom{4n}{2n}).
    -- Note: B_2n is non-zero for n >= 1.
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)

    -- The numerator of the simplified rational, guaranteed to be positive for n >= 1.
    Q_n.num.natAbs

open Complex

-- Helper function for the conjecture, $t(n) = \zeta(2n)/\zeta(n)^2$.
-- We use `Complex.riemannZeta` and take the real part, which is the correct real value for $s > 1$.
noncomputable def A114362_t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

open scoped Real

/--
A114362 Conjecture: (1 - t(n))/(1 + t(n)) = 1/2^n + 1/3^n + 1/5^n + 1/7^n + O(1/11^n),
where t(n) = zeta(2n)/zeta(n)^2. Cf. A348829.
This is formalized as the difference between the LHS and the sum of the first four inverse prime powers
being $O(1/11^n)$ as $n \to \infty$.
-/
theorem oeis_A114362_conjecture_1 :
    (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  sorry
