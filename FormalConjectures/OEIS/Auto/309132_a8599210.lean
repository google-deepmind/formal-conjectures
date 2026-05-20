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
A309132: $a(n)$ is the denominator of $F(n) = A027641(n-1)/n + A027642(n-1)/n^2$,
where $A027641(k)$ and A027642(k) are the numerator and denominator of the $k$-th standard Bernoulli number $B_k$ ($B_1 = -1/2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den

    -- F(n) = N / n + D / n^2, where division is rational division
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2

    F_n.den

/-- The A309132/Sondow conjecture: for $n > 1$, $a(n) = 1$ if and only if $n$ is prime. -/
def A309132_conjecture : Prop :=
  ∀ n : ℕ, 1 < n → (a n = 1 ↔ Nat.Prime n)

/--
The Agoh-Giuga condition for $n > 1$: $\sum_{k=1}^{n-1} k^{n-1} \equiv -1 \pmod n$.
We formalize this as $n$ dividing $\sum_{k=0}^{n-1} k^{n-1} + 1$ in $\mathbb{Z}$.
-/
def agoh_giuga_condition (n : ℕ) : Prop :=
  1 < n ∧ (n : ℤ) ∣ (Finset.sum (Finset.range n) (fun k : ℕ => (k : ℤ)^(n - 1)) + 1)

/-- The Agoh-Giuga conjecture: a number $n > 1$ is prime if and only if it satisfies the Agoh-Giuga condition. -/
def agoh_giuga_conjecture : Prop :=
  ∀ n : ℕ, 1 < n → (Nat.Prime n ↔ agoh_giuga_condition n)

/--
oeis_309132_conjecture_2: Is this conjecture equivalent to the Agoh-Giuga conjecture?
Formalizing the conjecture that the property $a(n) = 1 \iff \text{prime } n$ for $n>1$ (A309132_conjecture)
is equivalent to the Agoh-Giuga conjecture.
-/
theorem oeis_309132_conjecture_2 : A309132_conjecture ↔ agoh_giuga_conjecture := by sorry
