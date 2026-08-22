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
# Ben Green's Open Problem 82

Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many
$\theta \in \mathbb{R}/\mathbb{Z}$ must we have $\sum_{a \in A} \cos(a\theta) = 0$?

Convention: for $\theta \in \mathbb{R}/\mathbb{Z}$, identified with Mathlib's
`UnitAddCircle`, the symbol $\cos(a\theta)$ means $\cos(2\pi a \theta)$, i.e. the real
part of `fourier a θ`. Zeros are distinct points of the circle (not counted with
multiplicity). The open question asks for the guaranteed number of zeros: the
minimum, over all $A$ of size $n$, of that cardinality.

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.82)
- [Li68] J. E. Littlewood, Some Problems in Real and Complex Analysis, Heath, 1968, Problem 22.
- [BEFL08] P. Borwein, T. Erdélyi, R. Ferguson, R. Lockhart, On the zeros of cosine
  polynomials: solution to a problem of Littlewood, Ann. of Math. 167 (2008), 1109–1117.
- [JS21] T. Juškevičius, J. Sahasrabudhe, Cosine polynomials with few zeros,
  Bull. Lond. Math. Soc. 53 (2021), 877–892.
- [Sa19] J. Sahasrabudhe, Counting zeros of cosine polynomials: on a problem of
  Littlewood, Adv. Math. 343 (2019), 495–521.
- [Be25] B. Bedert, An improved lower bound for a problem of Littlewood on the zeros
  of cosine polynomials, arXiv:2407.16075.
-/

open Filter Real
open scoped Topology

namespace Green82

/--
The cosine polynomial of a finite set $A \subset \mathbb{Z}$, as a function on
$\mathbb{R}/\mathbb{Z}$. This is $\sum_{a \in A} \cos(2\pi a \theta)$, matching the
usual convention for $\theta \in \mathbb{R}/\mathbb{Z}$.
-/
noncomputable def cosinePolynomial (A : Finset ℤ) (θ : UnitAddCircle) : ℝ :=
  ∑ a ∈ A, (fourier a θ).re

/-- Distinct zeros of `cosinePolynomial A` on $\mathbb{R}/\mathbb{Z}$. -/
noncomputable def cosinePolynomialZeros (A : Finset ℤ) : Set UnitAddCircle :=
  {θ | cosinePolynomial A θ = 0}

/-- Number of distinct zeros on the circle. `Set.ncard` is `0` if the zero set is infinite. -/
noncomputable def numCosineZeros (A : Finset ℤ) : ℕ :=
  (cosinePolynomialZeros A).ncard

/--
The guaranteed number of zeros: the least number of distinct $\theta \in \mathbb{R}/\mathbb{Z}$
at which $\sum_{a \in A} \cos(a\theta) = 0$, over all $A \subset \mathbb{Z}$ of size $n$.
-/
noncomputable def minNumCosineZeros (n : ℕ) : ℕ :=
  sInf {numCosineZeros A | (A : Finset ℤ) (_ : A.card = n)}

/-- The empty set gives the zero function. -/
@[category test, AMS 11 42]
theorem cosinePolynomial_empty (θ : UnitAddCircle) :
    cosinePolynomial (∅ : Finset ℤ) θ = 0 := by
  simp [cosinePolynomial]

/-- A singleton $\{0\}$ gives the constant function $1$, hence no zeros. -/
@[category test, AMS 11 42]
theorem cosinePolynomial_singleton_zero (θ : UnitAddCircle) :
    cosinePolynomial ({0} : Finset ℤ) θ = 1 := by
  simp [cosinePolynomial]

/--
Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$
must we have $\sum_{a \in A} \cos(a\theta) = 0$?

Littlewood suggested “probably $n-1$, or not much less”. That guess is false: see the
solved bounds below. The unknown is the function of $n$ giving the guaranteed number of
zeros, not the disproved value $n-1$.
-/
@[category research open, AMS 11 42]
theorem green_82 : answer(sorry) = minNumCosineZeros := by
  sorry

/--
There are examples with at most $n^{5/6+o(1)}$ zeros, due to
Borwein, Erdélyi, Ferguson and Lockhart [BEFL08].
-/
@[category research solved, AMS 11 42]
theorem green_82.borwein_erdelyi_ferguson_lockhart :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)), ∀ᶠ n : ℕ in atTop,
      (minNumCosineZeros n : ℝ) ≤ (n : ℝ) ^ ((5 : ℝ) / 6 + o n) := by
  sorry

/--
This has been improved to $O(n^{2/3} \log^{2/3} n)$ by Juškevičius and Sahasrabudhe [JS21]
(equivalently $O((n \log n)^{2/3})$).
-/
@[category research solved, AMS 11 42]
theorem green_82.juskevicius_sahasrabudhe :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (minNumCosineZeros n : ℝ) ≤
        C * (n : ℝ) ^ ((2 : ℝ) / 3) * (log n) ^ ((2 : ℝ) / 3) := by
  sorry

/--
The number of zeros tends to infinity with $n$ [Sa19, Be25].
-/
@[category research solved, AMS 11 42]
theorem green_82.zeros_tendsto_atTop :
    Tendsto minNumCosineZeros atTop atTop := by
  sorry

/--
Sahasrabudhe [Sa19] obtained the lower bound $(\log\log\log n)^{1/2-o(1)}$.
-/
@[category research solved, AMS 11 42]
theorem green_82.sahasrabudhe :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)), ∀ᶠ n : ℕ in atTop,
      (log (log (log n))) ^ ((1 : ℝ) / 2 - o n) ≤ minNumCosineZeros n := by
  sorry

/--
Bedert [Be25] improved the lower bound to $(\log\log n)^{1-o(1)}$.
-/
@[category research solved, AMS 11 42]
theorem green_82.bedert :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)), ∀ᶠ n : ℕ in atTop,
      (log (log n)) ^ (1 - o n) ≤ minNumCosineZeros n := by
  sorry

end Green82
