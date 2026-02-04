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

/-!
# Erdős Problem 394

*References:*
- [erdosproblems.com/394](https://www.erdosproblems.com/394)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [ErHa78] Erdős, P. and Hall, R. R., On some unconventional problems on the divisors of integers.
  J. Austral. Math. Soc. Ser. A (1978), 479--485.
-/

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Erdos394

/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$ Is it true that
$\sum_{n\leq x}t_2(n)\ll \frac{x^2}{(\log x)^c}$ for some $c>0$?
-/
@[category research open, AMS 11]
theorem erdos_394_part_a :
    answer(sorry) ↔
      ∃ c > 0, (fun x ↦ ∑ n ∈ Ioc 1 ⌊x⌋₊,
      ((sInf { m : ℕ | 0 < m ∧ n ∣ m * (m + 1) } : ℕ) : ℝ)) =O[atTop]
      (fun x ↦ x ^ 2 / (Real.log x) ^ c) := by
  sorry

/--
Is it true that, for $k\geq 2$, $\sum_{n\leq x}t_{k+1}(n) =o\left(\sum_{n\leq x}t_k(n)\right)?$
-/
@[category research open, AMS 11]
theorem erdos_394_part_b :
    answer(sorry) ↔
      ∀ k ≥ 2, (fun (x : ℝ) ↦ ∑ n ∈ Ioc 1 ⌊x⌋₊,
      ((sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range (k + 1), (m + i) } : ℕ) : ℝ)) =o[atTop]
      (fun (x : ℝ) ↦ ∑ n ∈ Ioc 1 ⌊x⌋₊,
      ((sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) } : ℕ) : ℝ)) := by
  sorry

/--
In [ErGr80] they mention a conjecture of Erdős that the sum is $o(x^2)$. This was proved by Erdős
and Hall [ErHa78], who proved that in fact
$\sum_{n\leq x}t_2(n)\ll \frac{\log\log\log x}{\log\log x}x^2.$
-/
@[category research solved, AMS 11]
theorem erdos_394_hall_bound :
    (fun x ↦ ∑ n ∈ Ioc 1 ⌊x⌋₊, ((sInf { m : ℕ | 0 < m ∧ n ∣ m * (m + 1) } : ℕ) : ℝ)) =O[atTop]
    (fun x ↦ x ^ 2 * (Real.log (Real.log (Real.log x)) / Real.log (Real.log x))) := by
  sorry

/--
Erdős and Hall conjecture that the sum is $o(x^2/(\log x)^c)$ for any $c<\log 2$.
-/
@[category research open, AMS 11]
theorem erdos_394_hall_conjecture :
    ∀ c < Real.log 2, (fun x ↦ ∑ n ∈ Ioc 1 ⌊x⌋₊,
    ((sInf { m : ℕ | 0 < m ∧ n ∣ m * (m + 1) } : ℕ) : ℝ)) =o[atTop]
    (fun x ↦ x ^ 2 / (Real.log x) ^ c) := by
  sorry

/--
Since $t_2(p)=p-1$ for prime $p$ it is trivial that $\sum_{n\leq x}t_2(n)\gg \frac{x^2}{\log x}$.
-/
@[category research solved, AMS 11]
theorem erdos_394_lower_bound :
    (fun x ↦ x ^ 2 / Real.log x) =O[atTop]
    (fun x ↦ ∑ n ∈ Ioc 1 ⌊x⌋₊, ((sInf { m : ℕ | 0 < m ∧ n ∣ m * (m + 1) } : ℕ) : ℝ)) := by
  sorry

/--
Erdős and Hall [ErHa78] note that $t_{n-1}(n!)=2$.
-/
@[category research solved, AMS 11]
theorem erdos_394_factorial_n_minus_1 :
    ∀ (n : ℕ), n > 1 →
    sInf { m : ℕ | 0 < m ∧ (n !) ∣ ∏ i ∈ range (n - 1), (m + i) } = 2 := by
  sorry

/--
Erdős and Hall [ErHa78] note that $t_{n-2}(n!)\ll n$.
-/
@[category research solved, AMS 11]
theorem erdos_394_factorial_n_minus_2_upper :
    (fun (n : ℕ) ↦ ((sInf { m : ℕ | 0 < m ∧ (n !) ∣ ∏ i ∈ range (n - 2), (m + i) } : ℕ) : ℝ)) =O[atTop]
    (fun n ↦ (n : ℝ)) := by
  sorry

/--
$n=2^r$ shows that $t_{n-2}(n!)\ll n$ is the best possible (implying the lower bound is also linear).
-/
@[category research solved, AMS 11]
theorem erdos_394_factorial_n_minus_2_lower_pow2 :
    (fun (r : ℕ) ↦ (2 ^ r : ℝ)) =O[atTop]
    (fun r ↦ ((sInf { m : ℕ | 0 < m ∧ (2 ^ r) ! ∣ ∏ i ∈ range (2 ^ r - 2), (m + i) } : ℕ) : ℝ)) := by
  sorry

/--
Is it true that, for infinitely many $n$, $t_k(n!) < t_{k-1}(n!) - 1$ for all $1 \leq k < n$?
-/
@[category research open, AMS 11]
theorem erdos_394_factorial_gap_conjecture :
    answer(sorry) ↔
      Set.Infinite { n : ℕ | ∀ k, 2 ≤ k → k < n →
      sInf { m : ℕ | 0 < m ∧ (n !) ∣ ∏ i ∈ range k, (m + i) } <
      sInf { m : ℕ | 0 < m ∧ (n !) ∣ ∏ i ∈ range (k - 1), (m + i) } - 1 } := by
  sorry

/--
They proved (with Selfridge) that this holds for $n=10$.
-/
@[category research solved, AMS 11]
theorem erdos_394_factorial_gap_10 :
    ∀ (k : ℕ), 2 ≤ k → k < 10 →
    sInf { m : ℕ | 0 < m ∧ (10 !) ∣ ∏ i ∈ range k, (m + i) } <
    sInf { m : ℕ | 0 < m ∧ (10 !) ∣ ∏ i ∈ range (k - 1), (m + i) } - 1 := by
  sorry

end Erdos394
