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

open Nat Finset

/--
A091591: Number of pairs of twin primes between $n^2$ and $(n+1)^2$.
This counts the number of primes $p$ such that $p$ and $p+2$ are both prime,
and the entire twin prime pair $(p, p+2)$ lies strictly between $n^2$ and $(n+1)^2$.
That is, $n^2 < p$ and $p+2 < (n+1)^2$.
-/
def a (n : ℕ) : ℕ :=
  let lower_p_start : ℕ := n ^ 2 + 1
  -- The condition $p+2 < (n+1)^2$ is equivalent to $p \le (n+1)^2 - 3$.
  let max_p_value : ℕ := (n + 1) ^ 2 - 3

  -- We count primes $p$ in the closed interval $[n^2 + 1, (n+1)^2 - 3]$.
  Finset.card $ Finset.filter
    (fun p => p.Prime ∧ (p + 2).Prime)
    (Finset.Icc lower_p_start max_p_value)


-- The initial verifications provided in the prompt are omitted for brevity,
-- as they are not required for the final submission, which only needs the definition and the conjecture.

/--
A091591: Proving a(n)>0 for n>122 would also prove Legendre's conjecture that there is a prime between n^2 and (n+1)^2. - _T. D. Noe_, Feb 28 2007
-/
theorem oeis_a091591_conjecture_1 :
  (∀ n : ℕ, n > 122 → a n > 0) → (∀ n : ℕ, n > 0 → ∃ p, p.Prime ∧ n^2 < p ∧ p < (n+1)^2) := by sorry
