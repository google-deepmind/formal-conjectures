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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 360

*References:*
- [erdosproblems.com/360](https://www.erdosproblems.com/360)
- [AlEr96] Alon, Noga and Erdős, Paul, *Sure monochromatic subset sums*. Acta Arith. 74 (1996),
  269-272.
- [CFP21] Conlon, D. and Fox, J. and Pham, H. T., *Subset sums, completeness and colorings*.
  [arXiv:2104.14766](https://arxiv.org/abs/2104.14766) (2021).
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980).
- [Vu07] Vu, Van H., *Some new results on subset sums*. J. Number Theory 124 (2007), 229-233.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos360

/-- $f(n)$: the least number of classes in a partition of $\{1,\ldots,n-1\}$ such that $n$ is not
a sum of distinct elements of one class. A class contains $n$ among its subset sums exactly when
some finite subset of the class sums to $n$.

For $n \geq 2$ the partition into singletons is admissible (each element is less than $n$), so the
set is non-empty and `sInf` is its minimum. For $n \leq 1$ the set $\{1,\ldots,n-1\}$ is empty,
the empty partition is admissible, and $f(n) = 0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ P : Finpartition (Finset.Icc 1 (n - 1)),
    P.parts.card = r ∧ ∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ)}

/-- The answer: $\frac{n^{1/3}(n/\phi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}$. -/
noncomputable def erdos_360.answer (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
    (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ))

/--
Let $f(n)$ be minimal such that $\{1,\ldots,n-1\}$ can be partitioned into $f(n)$ classes so that
$n$ cannot be expressed as a sum of distinct elements from the same class. How fast does $f(n)$
grow?

A problem of Erdős and Graham [ErGr80]. Conlon, Fox, and Pham [CFP21, Theorem 1.5] determined
the order of growth of $f(n)$ up to a multiplicative constant, proving
$$f(n) \asymp \frac{n^{1/3}(n/\phi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}.$$
Here $\phi$ is Euler's totient function, and the statement is asymptotic ($n \to \infty$).
-/
@[category research solved, question value, AMS 5 11]
theorem erdos_360 : (fun n : ℕ ↦ (f n : ℝ)) =Θ[atTop] erdos_360.answer := by
  sorry

/--
Alon and Erdős [AlEr96] proved that $f(n) = n^{1/3+o(1)}$, and more precisely
$$\frac{n^{1/3}}{(\log n)^{4/3}}\ll f(n) \ll
  \frac{n^{1/3}}{(\log n)^{1/3}}(\log\log n)^{1/3}.$$
This is the two-sided bound, which implies the first claim.
-/
@[category research solved, AMS 5 11]
theorem erdos_360.variants.alon_erdos :
    (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (4 / 3 : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (f n : ℝ)) ∧
    (fun n : ℕ ↦ (f n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) *
          Real.log (Real.log n) ^ (1 / 3 : ℝ)) := by
  sorry

/--
Vu [Vu07] improved the lower bound to
$$f(n) \gg \frac{n^{1/3}}{\log n}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_360.variants.vu :
    (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n) =O[atTop] (fun n : ℕ ↦ (f n : ℝ)) := by
  sorry

end Erdos360
