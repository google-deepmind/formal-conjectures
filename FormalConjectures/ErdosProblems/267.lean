/-
Copyright 2025 Google LLC

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

/-!
# Erdős Problem 267

*Reference:* [erdosproblems.com/267](https://www.erdosproblems.com/267)
-/
/--
Let $F_1=F_2=1$ and $F_{n+1} = F_n + F_{n−1}$ be the Fibonacci sequence.
Let $n_1 < n_2 < ...$ be an infinite sequence with $\frac{n_{k+1}}{n_k} ≥ c > 1$. Must
$\sum_k \frac 1 {F_{n_k}}$ be irrational?
-/
@[category research open, AMS 11]
theorem erdos_267 (n : ℕ → ℕ)
    (hn : StrictMono n) (c : ℚ) (hc : 1 < c)
    (hnc : ∀ k, c ≤ n (k+1) / n k) :
    Irrational <| ∑' k, 1 / (Nat.fib <| n k) :=
  sorry

/--
Let $F_1=F_2=1$ and $F_{n+1} = F_n + F_{n−1}$ be the Fibonacci sequence.
Let $n_1 < n_2 < ...$ be an infinite sequence with $\frac {n_k}{k} → ∞$. Must
$\sum_k \frac 1 {F_{n_k}}$ be irrational?
-/
@[category research open, AMS 11]
theorem erdos_267.variants.generalisation_ratio_limit_to_infinity (n : ℕ → ℕ)
    (hn : StrictMono n)
    (hnc : Filter.Tendsto (fun k => (n (k+1) / k.succ : ℝ)) Filter.atTop Filter.atTop) :
    Irrational <| ∑' k, 1 / (Nat.fib <| n k) :=
  sorry

/--
Good [Go74] and Bicknell and Hoggatt [BiHo76] have shown that $\sum_n \frac 1 {F_{2^n}}$ is irrational.

Ref:
* [Go74] Good, I. J., _A reciprocal series of Fibonacci numbers_
* [BiHo76] Hoggatt, Jr., V. E. and Bicknell, Marjorie, _A reciprocal series of Fibonacci numbers with subscripts $2\sp{n}k$_
-/
@[category research solved, AMS 11]
theorem erdos_267.variants.specialization_pow_two :
    Irrational <| ∑' k, 1 / (Nat.fib <| 2^k) :=
  sorry


/--
The sum $\sum_n \frac 1 {F_{n}}$ itself was proved to be irrational by André-Jeannin.

Ref: André-Jeannin, Richard, _Irrationalité de la somme des inverses de certaines suites récurrentes_.
-/
@[category research solved, AMS 11]
theorem erdos_267.variants.fibonacci_inverse_sum :
    Irrational <| ∑' k, 1 / (Nat.fib k) :=
  sorry
