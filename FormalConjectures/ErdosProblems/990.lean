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

import FormalConjecturesUtil

/-!
# Erdős Problem 990

*References:*
- [erdosproblems.com/990](https://www.erdosproblems.com/990)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant, *Short proofs in
  combinatorics, probability, and number theory II*. arXiv:2604.06609 (2026).
- [ErTu50] Erdős, P. and Turán, P., *On the distribution of roots of polynomials*. Ann. of Math. (2)
  (1950), 105-119.
- [Ha72b] Hayman, W. K., *Angular value distribution of power series with gaps*. Proc. London Math.
  Soc. (3) (1972), 590-624.
-/

open Polynomial Classical

open scoped Real

namespace Erdos990

/--
The argument of a complex number, normalised to take values in the interval `[0, 2π)`.
-/
noncomputable def normArg (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z

/--
The number of roots of `f`, counted with multiplicity, whose argument lies in `I`.
-/
noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP (fun z => normArg z ∈ I)

/--
For $f = a_0 + \cdots + a_dx^d$, the quantity
$M=\frac{\lvert a_0\rvert+\cdots +\lvert a_d\rvert}{(\lvert a_0\rvert\lvert a_d\rvert)^{1/2}}$.
-/
noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

/--
Let $f=a_0+\cdots+a_dx^d\in \mathbb{C}[x]$ be a polynomial. Is it true that, if $f$ has roots
$z_1,\ldots,z_d$ with corresponding arguments $\theta_1,\ldots,\theta_d\in [0,2\pi]$, then for all
intervals $I\subseteq [0,2\pi]$
\[
\left\lvert (\# \theta_i \in I) - \frac{\lvert I\rvert}{2\pi}d\right\rvert \ll
\left(n\log M\right)^{1/2},
\]
where $n$ is the number of non-zero coefficients of $f$ and
\[
M=\frac{\lvert a_0\rvert+\cdots +\lvert a_d\rvert}{(\lvert a_0\rvert\lvert a_d\rvert)^{1/2}}.
\]

An internal OpenAI model (see [APSSV26b]) has disproved the conjecture, constructing, for every
$n\geq 1$, a polynomial $f$ with $n$ non-zero coefficients such that $M<3$ and with a positive real
zero of multiplicity $n-1$, whence letting $I=[0,c/d]$ for a suitably small $c>0$,
\[
\left\lvert (\# \theta_i \in I) - \frac{\lvert I\rvert}{2\pi}d\right\rvert \geq n-1.
\]
-/
@[category research solved, AMS 12 30]
theorem erdos_990 : answer(False) ↔
    ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f)) := by
  sorry

/--
Erdős and Turán [ErTu50] proved such an upper bound with $n$ replaced by $d$.
-/
@[category research solved, AMS 12 30]
theorem erdos_990.variants.erdos_turan :
    ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        C * Real.sqrt ((f.natDegree : ℝ) * Real.log (M f)) := by
  sorry

/--
Hayman [Ha72b] proved
\[
\left\lvert (\# \theta_i \in I) - \frac{\lvert I\rvert}{2\pi}d\right\rvert \leq n-1,
\]
and noted this is essentially sharp since $f(x)=(x^{p}-1)^{n-1}$ has $n$ non-zero coefficients and
has $1$ as a positive real zero of multiplicity $n-1$ (although for this $f$ the parameter $M$
becomes very large).
-/
@[category research solved, AMS 12 30]
theorem erdos_990.variants.hayman :
    ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
      |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
        (f.support.card : ℝ) - 1 := by
  sorry

/--
An internal OpenAI model (see [APSSV26b]) has disproved the conjecture, constructing, for every
$n\geq 1$, a polynomial $f$ with $n$ non-zero coefficients such that $M<3$ and with a positive real
zero of multiplicity $n-1$.
-/
@[category research solved, AMS 12 30]
theorem erdos_990.variants.counterexample :
    ∀ n : ℕ, 1 ≤ n → ∃ f : ℂ[X], f.coeff 0 ≠ 0 ∧ f.support.card = n ∧ M f < 3 ∧
      ∃ x : ℝ, 0 < x ∧ f.rootMultiplicity (x : ℂ) = n - 1 := by
  sorry

end Erdos990
