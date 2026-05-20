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
A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$
-/
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

-- Defining the denominator product: $\prod_{k=0}^{r-1} (8n - (2k+1))$ in ℤ
/-- The denominator product $(8n - 1)(8n - 3) \cdots (8n - (2r - 1))$,
defined as $\prod_{k=0}^{r-1} (8n - (2k+1))$ in $\mathbb{Z}$. -/
def denominator_product (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ)) |>.prod

/--
A211420: It also appears that a(n) is divisible by 8*n - 1 for all n. More generally, we
conjecture that there are constants K(r), r >= 0, such that
$a(n) \cdot K(r)/((8*n - 1)*(8*n - 3)*...*(8*n - (2*r+1)))$ is an integer for all n.
-/
theorem oeis_211420_conjecture_1 : ∀ r : ℕ, ∃ K : ℤ, K > 0 ∧ ∀ n : ℕ,
    denominator_product n r ∣ (a n : ℤ) * K := by
  sorry
