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

open Nat Finset ArithmeticFunction

/--
A233864: $a(n) = |\left\{0 < m < 2n: m = \sigma_1(k) \text{ for some } k>0, \text{ and } 2n - 1 - m \text{ and } 2n - 1 + m \text{ are both prime}\right\}|$, where $\sigma_1(k)$ is the sum of all positive divisors of $k$.
-/
noncomputable def A233864_a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let twice_n : ℕ := 2 * n
  let N : ℕ := twice_n - 1

  -- The set of $k$ values we consider is $\{1, 2, \ldots, 2n-1\}$.
  let k_domain : Finset ℕ := Finset.Ico 1 twice_n

  -- The set of $m$ values is the image of $\sigma_1$ over the domain.
  let sigma_values : Finset ℕ := k_domain.image (sigma 1)

  (sigma_values.filter (fun m : ℕ =>
    m < twice_n ∧
    -- Ensure $N - m > 0$. Since $N=2n-1$, this is $m < 2n-1$.
    m < N ∧
    (N - m).Prime ∧
    (N + m).Prime
  )) |>.card

/--
Conjecture A233864 (i): $a(n) > 0$ for all $n > 3$.
-/
theorem A233864_conjecture_i : ∀ n : ℕ, 3 < n → A233864_a n > 0 := by
  sorry
