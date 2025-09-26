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
open scoped ArithmeticFunction

namespace Erdos975

/-
Sum of $\tau(f(n))$ for a function $f : \mathbb{N} \to \mathbb{N}$.
Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
-/
noncomputable def Erdos975Sum (f : ℕ → ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), σ 0 (f n)

/- Auxiliary definition for nonnegative irreducible polynomials over $\mathbb{Z}$ on $\mathbb{N}$. -/
def Erdos975NonnegIrredPoly (f : ℕ → ℕ) (g : ℤ[X]) : Prop :=
  Irreducible g ∧ ∃ N : ℕ, ∀ n ≥ N, f n = g.eval ↑n ∧ 0 ≤ f n

def Erdos975Asymptotic (f : ℕ → ℕ) (c : ℝ) : Prop :=
  Tendsto (fun x ↦ Erdos975Sum f x / (x * x.log)) (atTop) (nhds c)

/--
For an irreducible polynomial $f \in \mathbb{Z}[x]$ with $f(n) \ge 0$ for all $n \ge 0$,
does there exists a constant $c = c(f) > 0$ such that
$\sum_{n \le x} \tau(f(n)) \approx c \cdot x \log x$?
-/
@[category research open, AMS 11]
theorem erdos_975 (f : ℕ → ℕ) (g : ℤ[X]) (hf : Erdos975NonnegIrredPoly f g) :
    ∃ (c : ℝ), 0 < c ∧ Erdos975Asymptotic f c := by
  sorry

/--
The correctness of growth rate is shown in [Va39] (lower bound) and [Er52b] (upper bound).
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.upper_bound (f : ℕ → ℕ) (g : ℤ[X]) (hf : Erdos975NonnegIrredPoly f g) :
    Erdos975Sum f =O[atTop] (fun x ↦ x * x.log) := by
  sorry

@[category research solved, AMS 11]
theorem erdos_975.variant.lower_bound (f : ℕ → ℕ) (g : ℤ[X]) (hf : Erdos975NonnegIrredPoly f g) :
    (fun x ↦ x * x.log) =O[atTop] (Erdos975Sum f) := by
  sorry

/--
When $f$ is an irreducible quadratic polynomial, the question is answered first by Hooley [Ho63].
More compact expression of the constant in terms of Hurwitz class numbers (when $a = 1$)
is given by McKey in [Mc95], [Mc97], [Mc99].

TODO: formalize Hurwitz class numbers and the expression of the constant in terms of them.
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.quadratic (f : ℕ → ℕ) (g : ℤ[X]) (hf : Erdos975NonnegIrredPoly f g)
    (hg_degree : g.degree = 2) :
    ∃ (c : ℝ), 0 < c ∧ Erdos975Asymptotic f c := by
  sorry

/--
More concrete example for $f(n) = n^2 + 1$, where the asymptote is
$\sum_{n \le x} \tau(n^2 + 1) \sim \frac{3}{\pi} x \log x + O(x)$. See Tao's blog [T].
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.n2_plus_1_strong :
    (fun x ↦ (Erdos975Sum (fun n ↦ n ^ 2 + 1) x - (3 / π) * x * x.log)) =O[atTop] id := by
  sorry

@[category research solved, AMS 11]
theorem erdos_975.variant.n2_plus_1 :
    Erdos975Asymptotic (fun n ↦ n ^ 2 + 1) (3 / π) := by
  sorry

end Erdos975
