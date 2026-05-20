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
A003958 is a multiplicative function defined by $A003958(p^e) = (p-1)^e$ for a prime power $p^e$.
For $n = \prod p_i^{e_i}$, $A003958(n) = \prod (p_i - 1)^{e_i}$.
-/
def A003958 (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => (p - 1) ^ e

/--
A351442: $a(n) = A003958(\sigma(n))$, where $A003958$ is multiplicative with $a(p^e) = (p-1)^e$
and $\sigma$ is the sum of divisors function.
-/
def a (n : ℕ) : ℕ :=
  A003958 (ArithmeticFunction.sigma 1 n)


theorem a_one : a 1 = 1 := by
  simp_all[a]
  norm_num[ArithmeticFunction.sigma, A003958]

theorem a_two : a 2 = 2 := by
  (inhabit ℝ)
  rw[a]
  norm_num[ArithmeticFunction.sigma, A003958]

theorem a_three : a 3 = 1 := by
  delta a
  norm_num [ArithmeticFunction.sigma, A003958]
  norm_num[Nat.primeFactors,←(4).primeFactorsList_count_eq, Finsupp.prod,Nat.primeFactorsList]

theorem a_four : a 4 = 6 := by
  delta a
  inhabit ℝ
  norm_num[ArithmeticFunction.sigma, A003958,show(4).divisors={1,2,4}by decide]


/--
oeis_351442_conjecture_0: Question: Are there more fixed points than 1, 2, 8, 128, 288, 720, 32768, 29719872, ..., 2147483648 ?
This theorem conjectures that these numbers are exactly the positive fixed points of the sequence $a(n)$.
The list of fixed points is taken verbatim from the OEIS entry.
-/
theorem oeis_351442_conjecture_0 :
  ∀ n : ℕ, n > 0 → (a n = n ↔ n ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ)) := by
  sorry
