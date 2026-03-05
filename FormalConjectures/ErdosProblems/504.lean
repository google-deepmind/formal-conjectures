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
# Erdős Problem 504

Determine the maximum guaranteed angle α_N for N-point planar sets: the supremum of all
angles α such that every set of N points in the plane contains three distinct points forming
an angle of at least α.

*Reference:* [erdosproblems.com/504](https://www.erdosproblems.com/504)
-/

namespace Erdos504

/--
The angle at point $y$ determined by three points $x$, $y$, $z$ in $\mathbb{R}^2$:
the angle between vectors $(x - y)$ and $(z - y)$, computed as
$\arccos$ of their normalized inner product. Returns a value in $[0, \pi]$.
-/
noncomputable def angleAt (x y z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let u := x - y
  let v := z - y
  Real.arccos (@inner ℝ _ _ u v / (‖u‖ * ‖v‖))

/--
$\alpha_N$: the maximum guaranteed angle for $N$-point planar sets.
The supremum of all $\alpha \in [0, \pi]$ such that every set of $N$ points in $\mathbb{R}^2$
contains three distinct points $x$, $y$, $z$ with angle at $y$ at least $\alpha$.
-/
noncomputable def maxGuaranteedAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | 0 ≤ α ∧ α ≤ Real.pi ∧
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card = N →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        angleAt x y z ≥ α}

/--
Erdős Problem 504 (Blumenthal's problem, solved by Sendov):

Let $\alpha_N$ be the supremum of all $0 \leq \alpha \leq \pi$ such that in every set
$A \subset \mathbb{R}^2$ of size $N$ there exist three distinct points $x, y, z \in A$
such that the angle at $y$ (between rays $yx$ and $yz$) is at least $\alpha$.
Determine $\alpha_N$.

Sendov (1993) proved that for $n \geq 3$ and $2^{n-1} < N \leq 2^n$:
$$\alpha_N = \pi(1 - 1/n) \quad \text{when } N > 2^{n-1} + 2^{n-3}$$
$$\alpha_N = \pi(1 - 1/(2n-1)) \quad \text{when } N \leq 2^{n-1} + 2^{n-3}$$
-/
@[category research solved, AMS 52]
theorem erdos_504 :
    ∀ (N : ℕ), 4 < N →
    ∀ (n : ℕ), 3 ≤ n → 2 ^ (n - 1) < N → N ≤ 2 ^ n →
      maxGuaranteedAngle N =
        answer(if 2 ^ (n - 1) + 2 ^ (n - 3) < N
          then Real.pi * (1 - 1 / (n : ℝ))
          else Real.pi * (1 - 1 / (2 * (n : ℝ) - 1))) := by
  sorry

end Erdos504
