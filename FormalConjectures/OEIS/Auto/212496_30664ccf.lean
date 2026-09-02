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

open BigOperators Finset Nat Real

/--
The total number of prime factors of $k$, counted with multiplicity, denoted $\Omega(k)$.
-/
def omega_mult (k : ℕ) : ℕ :=
  k.factorization.sum (fun _ e => e)

/--
A212496: $a(n) = \sum_{k=1}^n (-1)^{k-\Omega(k)}$ with $\Omega(k)$ the total number of prime factors of $k$ (counted with multiplicity).
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (Icc 1 n) fun k =>
    -- The term is $(-1)^{k - \Omega(k)}$. We use parity check on the integer exponent.
    let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
    if exponent % 2 = 0 then 1 else -1

/--
The related sequence $b(n) = \sum_{k=1}^n \frac{(-1)^{k-\Omega(k)}}{k}$, formalized as a sum in $\mathbb{R}$.
This function is noncomputable because it returns a real number.
-/
noncomputable
def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

-- We remove the failing proofs for a_n and keep the definition of a(n) as provided.

/--
Sun also conjectured that $b(n) = \sum_{k=1}^n (-1)^{k-\Omega(k)}/k < 0$ for all $n=1,2,3, \dots$.
Moreover, he guessed that $b(n) < -1/\sqrt{n}$ for all $n > 1$, and $b(n) > -\log(\log(n))/\sqrt{n}$ for $n > 2008$.
Note: $n$ must be large enough for $\log(\log(n))$ to be well-defined, i.e., $n > e \approx 2.718$. The conjecture's limit $n > 2008$ is certainly sufficient.
-/
theorem oeis_212496_conjecture_1 (n : ℕ) :
  (n > 0 → b n < 0) ∧
  (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
  (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)) :=
by sorry
