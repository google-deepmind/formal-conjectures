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
# Erdős Problem 1131

*References:*
- [erdosproblems.com/1131](https://www.erdosproblems.com/1131)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  6 (1961), 221–254.
- [ESVV94] Erdős, P., Szabados, J., Varma, A. K., and Vértesi, P.,
  *On an interpolation theoretical extremal problem*. Studia Sci. Math. Hungar. 29
  (1994), 55–60.
- [Er95e] Erdős, Paul, *Some old and new problems in approximation theory*.
  Constr. Approx. 11 (1995), 419–421.
- [Fe32] Fejér, Leopold, *Bestimmung derjenigen Abszissen eines Intervalles, für welche die
  Quadratsumme der Grundfunktionen der Lagrangeschen Interpolation im Intervalle ein
  möglichst kleines Maximum besitzt*. Ann. Scuola Norm. Super. Pisa Cl. Sci. (2)
  1 (1932), 263–276.
- [Sz66] Szabados, J., *On a problem of P. Erdős*. Acta Math. Acad. Sci. Hungar.
  17 (1966), 155–157.
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

open scoped BigOperators Interval
open Filter Set

namespace Erdos1131

/-- An injective tuple of interpolation nodes in $[-1,1]$. -/
def Admissible {n : ℕ} (x : Fin n ↪ ℝ) : Prop :=
  ∀ k, x k ∈ Set.Icc (-1 : ℝ) 1

/-- The integral of the sum of the squared Lagrange basis polynomials. -/
noncomputable def functional {n : ℕ} (x : Fin n ↪ ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    ∑ k : Fin n,
      ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2

/-- The values of `functional` attained by admissible $n$-tuples. -/
def values (n : ℕ) : Set ℝ :=
  {y | ∃ x : Fin n ↪ ℝ, Admissible x ∧ functional x = y}

/-- The infimum of `functional` over admissible $n$-tuples. -/
noncomputable def M (n : ℕ) : ℝ :=
  sInf (values n)

/-- The scaled defect whose proposed limit is the asymptotic subquestion in Problem 1131. -/
noncomputable def scaledDefect (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (2 - M (n + 1))

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
\[
l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},
\]
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

What is the minimal value of
\[
I(x_1,\ldots,x_n)=\int_{-1}^1 \sum_k \lvert l_k(x)\rvert^2\mathrm{d}x?
\]
In particular, is it true that
\[
\min I =2-(1+o(1))\frac{1}{n}?
\]

Erdős first conjectured this minimum was achieved by taking the $x_i$ to be the roots of
the integral of the Legendre polynomial, since Fejér [Fe32] had earlier shown these to be
minimisers of
\[
\max_{x\in [-1,1]}\sum_k \lvert l_k(x)\rvert^2.
\]
This was disproved by Szabados [Sz66] for every $n>3$.

Erdős, Szabados, Varma, and Vértesi [ESVV94] proved that
\[
2-O\left(\frac{(\log n)^2}{n}\right)\leq \min I\leq 2-\frac{2}{2n-1},
\]
where the upper bound is witnessed by the roots of the integral of the Legendre polynomial
as above.

The asymptotic subquestion has a negative answer. The linked formal proof uses the roots of
$T_n-\frac16T_{n-2}$ as an explicit admissible comparison family and proves that, for every
$N\geq 24780$,
\[
\frac{106}{105}\leq (N+1)(2-M(N+1)),
\]
so the scaled defect cannot tend to $1$.
-/
@[category research solved, AMS 28 41 65,
  formal_proof using lean4 at "https://github.com/seanm27lol/erdos-1131-lean/blob/31574acf09ae50430c08da92288800fe7d26c7fd/Erdos1131/Main.lean"]
theorem erdos_1131 :
    answer(False) ↔ Tendsto scaledDefect atTop (nhds 1) := by
  sorry

end Erdos1131
