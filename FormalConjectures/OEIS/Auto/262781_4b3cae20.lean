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
open scoped Nat.Prime

/--
A262781: Number of ordered ways to write $n$ as $x^2 + \phi(y^2) + \phi(z^2)$
($x \ge 0$ and $0 < y \le z$) with $y$ or $z$ prime, where $\phi(\cdot)$ is Euler's totient function.
-/
def A262781 (n : ℕ) : ℕ :=
  -- Define the cartesian product of search ranges for (x, y, z).
  -- $x$ is bounded by $\sqrt{n}$. $y, z$ are conservatively bounded by $n$.
  let R_x := Finset.range (Nat.sqrt n + 1)
  let R_y_z := (Finset.range (n + 1)).product (Finset.range (n + 1))

  Finset.card $
  (R_x.product R_y_z)
  |>.filter (fun p =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    -- Constraints: $0 < y \le z$
    0 < y ∧ y ≤ z ∧
    -- Primality: $y$ or $z$ is prime
    (y.Prime ∨ z.Prime) ∧
    -- Equation: $n = x^2 + \phi(y^2) + \phi(z^2)$
    x^2 + totient (y ^ 2) + totient (z ^ 2) = n
  )

/-- The set of integers $n$ for which $A262781(n)=1$. -/
private def A262781_unit_set : Finset ℕ :=
  {3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649}

/--
The formal statement of Conjecture A262781.
(i) a(n) > 0 for all n > 6, and a(n) = 1 only for n in A262781_unit_set.
(ii) For any integer n > 4, $2n$ can be written as $\phi(p^2) + \phi(x^2) + \phi(y^2)$ with $p$ prime and $p \le x \le y$.
-/
def oeis_A262781_conjecture_statement : Prop :=
  -- Part (i)
  (∀ n : ℕ, 6 < n → 0 < A262781 n) ∧
  (∀ n : ℕ, A262781 n = 1 ↔ n ∈ A262781_unit_set) ∧
  -- Part (ii)
  (∀ n : ℕ, 4 < n →
    ∃ (p x y : ℕ),
      p.Prime ∧ 0 < x ∧ 0 < y ∧ -- Since the totient function is used, it is good practice to ensure the base is positive, although p prime implies p >= 2.
      p ≤ x ∧ x ≤ y ∧
      totient (p ^ 2) + totient (x ^ 2) + totient (y ^ 2) = 2 * n)

/--
Conjecture from OEIS A262781:
(i) a(n) > 0 for all n > 6, and a(n) = 1 only for n = 3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649.
(ii) For any integer n > 4, we can write 2*n as phi(p^2) + phi(x^2) + phi(y^2) with p prime and p <= x <= y.
-/
theorem oeis_A262781_conjecture : oeis_A262781_conjecture_statement := by sorry
