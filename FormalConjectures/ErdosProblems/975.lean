/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 975

*References:*
 - [erdosproblems.com/975](https://www.erdosproblems.com/975)
 - [Va39] van der Corput, J. G., Une in\'egalit\'e{} relative au nombre des diviseurs. Nederl. Akad. Wetensch., Proc. (1939), 547--553.
 - [Er52b] Erd\"os, P., On the sum {$\sum^x_{k=1} d(f(k))$}. J. London Math. Soc. (1952), 7--15.
 - [Ho63] Hooley, Christopher, On the number of divisors of a quadratic polynomial. Acta Math. (1963), 97--114.
 - [Mc95] McKee, James, On the average number of divisors of quadratic polynomials. Math. Proc. Cambridge Philos. Soc. (1995), 389--392.
 - [Mc97] McKee, James, A note on the number of divisors of quadratic polynomials. (1997), 275--281.
 - [Mc99] McKee, James, The average number of divisors of an irreducible quadratic polynomial. Math. Proc. Cambridge Philos. Soc. (1999), 17--22.
 - [T] T. Tao, Erdos' divisor bound, https://terrytao.wordpress.com/2011/07/23/erdos-divisor-bound/
-/

open Filter Real Polynomial
open scoped ArithmeticFunction.sigma Topology

namespace Erdos975

/-- Sum of $\tau(f(n))$ from `0` to `⌊x⌋` for a polynomial $f \in \mathbb{Z}[X]$.

Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
Also, for simplicity, we use `Nat.floor` to convert rational values to natural numbers, instead of
dealing with negative values. -/
noncomputable def Erdos975Sum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval ↑n⌋₊

/--
For an irreducible polynomial $f \in \mathbb{Z}[x]$ with $f(n) \ge 1$ for sufficiently large $n$,
does there exists a constant $c = c(f) > 0$ such that
$\sum_{n \le x} \tau(f(n)) \approx c \cdot x \log x$?

Note that it is unclear whether the polynomial should have integer coefficients or merely be
integer-valued. We assume the former. -/
@[category research open, AMS 11]
theorem erdos_975 : answer(sorry) ↔
    ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f → (∀ᶠ n in atTop, 1 ≤ f.eval n) →
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  sorry

/--
The correctness of the growth rate is shown in [Va39] (lower bound) and [Er52b] (upper bound).
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.upper_bound (f : ℤ[X]) (hf : Irreducible f)
    (hf_pos : ∀ᶠ n in atTop, 1 ≤ f.eval n) : Erdos975Sum f =O[atTop] (fun x ↦ x * log x) := by
  sorry

@[category research solved, AMS 11]
theorem erdos_975.variant.lower_bound (f : ℤ[X]) (hf : Irreducible f) (hfdeg : f.natDegree ≠ 0)
    (hf_pos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    (fun x ↦ x * log x) =O[atTop] Erdos975Sum f := by
  sorry

/--
When $f$ is an irreducible quadratic polynomial, the question is answered first by Hooley [Ho63].
More compact expression of the constant in terms of Hurwitz class numbers (when $a = 1$)
is given by McKey in [Mc95], [Mc97], [Mc99].

TODO: formalize Hurwitz class numbers and the expression of the constant in terms of them.
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.quadratic (f : ℤ[X]) (hf : Irreducible f)
    (hf_pos : ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval ↑n) (hf_degree : f.degree = 2) (c : ℝ) :
    c = answer(sorry) → 0 < c ∧ Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  sorry

/--
More concrete example for $f(n) = n^2 + 1$, where the asymptote is
$\sum_{n \le x} \tau(n^2 + 1) \sim \frac{3}{\pi} x \log x + O(x)$. See Tao's blog [T].
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.n2_plus_1_strong :
    (fun x ↦ Erdos975Sum (X ^ 2 + 1) x - (3 / π) * x * log x) =O[atTop] id := by
  sorry

@[category research solved, AMS 11]
theorem erdos_975.variant.n2_plus_1 :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975Sum (X ^ 2 + 1) x / (x * log x)) atTop (𝓝 c) := by
  sorry

end Erdos975
