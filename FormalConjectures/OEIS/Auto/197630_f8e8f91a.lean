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
open BigOperators Nat Int

/--
The $\mathbb{Z}$ definition of the Fermat quotient $q_p(k) = (k^{p-1}-1)/p$.
-/
def fermat_quotient_int (k p : ℕ) : ℤ := (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))

/--
The $\mathbb{Z}$ definition of the Wilson quotient $w_p = ((p-1)!+1)/p$.
-/
def wilson_quotient_int (p : ℕ) : ℤ := ((p - 1).factorial + 1) / (p : ℤ)

/--
A197630: Lerch quotients of odd primes:
$$\frac{\left(\sum_{k=1}^{p-1} q_p(k)\right) - w_p}{p}$$
where $q_p(k) = (k^{p-1}-1)/p$ is a Fermat quotient, $w_p = ((p-1)!+1)/p$ is a Wilson quotient,
and $p$ is the $n$-th prime, with $n > 1$.
The index $n$ corresponds to the $n$-th prime $p_n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if 1 < n then
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let p_z : ℤ := p_n
    -- Summation over k=1 to p_n - 1, represented by k in {0..p_n-2} using k+1.
    let sum_q : ℤ := Finset.sum (Finset.range (p_n - 1)) (fun k : ℕ => fermat_quotient_int (k + 1) p_n)
    let L_p : ℤ := sum_q - wilson_quotient_int p_n
    (L_p / p_z).natAbs
  else
    0

/--
Conjecture A197630: Is 13 the only Lerch quotient that is itself prime?
The sequence $a(n)$ is the Lerch quotient, and 13 is the value for $n=3$ (prime $p=5$).
-/
theorem oeis_197630_conjecture_0 : ∀ n : ℕ, 1 < n → Nat.Prime (a n) → a n = 13 := by sorry
