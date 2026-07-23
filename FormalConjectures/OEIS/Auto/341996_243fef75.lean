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

/-- The arithmetic derivative $D(n)$, A003415 in OEIS.
$D(0) = 0$, $D(1) = 0$.
For $n > 1$ with prime factorization $n = \prod p_i^{e_i}$,
$D(n) = \sum_{i} e_i \cdot \frac{n}{p_i}$.
-/
def arithmetic_derivative (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else
    (n.primeFactors).sum fun p =>
      (n.factorization p) * (n / p)

/--
A341996: $a(n) = 1$ if there is at least one such prime $p$ that $p^p$ divides the arithmetic derivative of $n$, $\text{A003415}(n)$; $a(0) = a(1) = 0$ by convention.
-/
def A341996 (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else
    let d := arithmetic_derivative n
    -- We only need to check primes $p \le d+1$, since $p^p$ grows very fast.
    -- Using `range (d + 1)` is a heuristic upper bound for primes to check.
    let primes_to_check := (range (d + 2)).filter Nat.Prime -- checking up to d+1 (since p <= d+1 implies p <= d or p=d+1)

    -- Check for existence by filtering the set of primes and checking for non-emptiness.
    if (primes_to_check.filter fun p => (p ^ p) ∣ d).Nonempty then 1 else 0


theorem a_zero : A341996 0 = 0 := by
  unfold A341996; simp

theorem a_one : A341996 1 = 0 := by
  unfold A341996; simp

/--
Conjecture (OEIS A341996 Question): What is the asymptotic mean of this sequence and its complement A368915?
This formalizes the belief that the natural density (asymptotic mean) of the set of numbers $n$ for which $A341996(n)=1$ exists.
-/
theorem oeis_341996_conjecture_0 :
  ∃ c : ℝ, ({n : ℕ | A341996 n = 1} : Set ℕ).HasDensity c :=
by sorry