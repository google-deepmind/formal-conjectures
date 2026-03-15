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
# Erdős Problem 391

Let $t(n)$ be the maximal value such that $n!$ can be written as a product
of $n$ positive integers, each at least $t(n)$. Erdős conjectured that
$t(n)/n \to 1/e$.

Erdős, Selfridge, and Straus claimed to have proved the corresponding lower bound,
but the proof was lost after Straus's death and could never be reconstructed.
The full conjecture (and more) was resolved by Alexeev, Conway, Rosenfeld, Sutherland,
Tao, Uhr, and Ventullo [ACRSTUV25], who proved that
$t(n)/n = 1/e - c_0/\log n + O(1/(\log n)^{1+c})$ where $c_0 = 0.3044\cdots$
is an explicit constant.

## References

* [ACRSTUV25] Alexeev, B., Conway, E., Rosenfeld, M., Sutherland, A., Tao, T., Uhr, M.,
  Ventullo, K., _Decomposing a factorial into large factors_. arXiv:2503.20170 (2025).
* [AlGr77] Alladi, K., Grinstead, C., _On the decomposition of n! into prime powers_.
  J. Number Theory **9** (1977), 452–458.
* [Er96b] Erdős, P., _Some problems I presented or planned to present in my short talk_.
  Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333–335.
* [Gu04] Guy, R.K., _Unsolved problems in number theory_. (2004), xviii+437.
* [GuSe98] Guy, R.K., Selfridge, J.L., _Factoring Factorial n_.
  Amer. Math. Monthly **105** (1998), 766–767.

OEIS: [A034258](https://oeis.org/A034258), [A034259](https://oeis.org/A034259)

*Reference:* [erdosproblems.com/391](https://www.erdosproblems.com/391)
-/

open BigOperators Filter

namespace Erdos391

/--
A valid representation of $n!$ as a product of $n$ positive integers in
non-decreasing order.
-/
def IsFactorialRepr (n : ℕ) (f : Fin n → ℕ) : Prop :=
  (∀ i, 0 < f i) ∧ Monotone f ∧ ∏ i, f i = n.factorial

/--
$t(n)$ is the maximal value of the smallest factor in any representation of $n!$
as a product of $n$ positive integers in non-decreasing order.
-/
noncomputable def erdos391_t (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ f : Fin n → ℕ, IsFactorialRepr n f ∧ ∀ i, k ≤ f i}

/--
Let $t(n)$ be maximal such that $n! = a_1 \cdots a_n$ with
$t(n) = a_1 \leq \cdots \leq a_n$.
The limit of $t(n)/n$ as $n \to \infty$ equals $1/e$.
-/
@[category research solved, AMS 11]
theorem erdos_391 :
    Tendsto (fun n : ℕ => (erdos391_t n : ℝ) / (n : ℝ))
      atTop (nhds (1 / Real.exp 1)) := by
  sorry

/--
There exists a constant $c > 0$ such that $t(n)/n \leq 1/e - c/\log(n)$ for
infinitely many $n$.
-/
@[category research solved, AMS 11]
theorem erdos_391.variants.rate_of_convergence :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (erdos391_t n : ℝ) / (n : ℝ) ≤ 1 / Real.exp 1 - c / Real.log (n : ℝ) := by
  sorry

end Erdos391
