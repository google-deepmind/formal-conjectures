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
# Erdős Problem 605

*Reference:* [erdosproblems.com/605](https://www.erdosproblems.com/605)

Is there some function $f(n)\to \infty$ as $n\to\infty$ such that there exist $n$ distinct
points on the surface of a two-dimensional sphere with at least $f(n)n$ many pairs of
points whose distances are the same?

This was solved by Erdős, Hickerson, and Pach [EHP89], who showed $u_{\sqrt{2}}(n) \asymp
n^{4/3}$ and $u_D(n) \gg n \log^* n$ for all $D > 1$. The lower bound was improved by
Swanepoel and Valtr [SwVa04] to $u_D(n) \gg n\sqrt{\log n}$. The best upper bound for
general $D$ is $u_D(n) \ll n^{4/3}$.

[EHP89] Erdős, P., Hickerson, D., and Pach, J., _A problem of Leo Moser about repeated
distances on the sphere_. Amer. Math. Monthly 96 (1989), 569–575.

[SwVa04] Swanepoel, K. J. and Valtr, P., _The unit distance problem on spheres_.
In Towards a Theory of Geometric Graphs (2004), 145–160.

[Er85] Erdős, P., _Problems and results in combinatorial geometry_. Discrete geometry and
convexity (New York, 1982), Ann. New York Acad. Sci. 440 (1985), 1–11.
-/

open Filter

namespace Erdos605

/-- The number of ordered pairs of distinct points from $A$ at Euclidean distance $d$. -/
noncomputable def pairsAtDistance
    (A : Finset (EuclideanSpace ℝ (Fin 3))) (d : ℝ) : ℕ :=
  (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card

/--
Erdős Problem 605 [Er85]:

There exists a function $f(n) \to \infty$ such that for all $n \geq 2$, one can place $n$ distinct
points on the surface of a sphere in $\mathbb{R}^3$ with at least $f(n) \cdot n$ ordered pairs of
points at some common distance. (Equivalently, at least $f(n) \cdot n / 2$ unordered pairs.)
-/
@[category research solved, AMS 5 52]
theorem erdos_605 : answer(True) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ n : ℕ, n ≥ 2 →
        ∃ (R : ℝ) (A : Finset (EuclideanSpace ℝ (Fin 3))),
          R > 0 ∧ A.card = n ∧
          (∀ x ∈ A, ‖x‖ = R) ∧
          ∃ d : ℝ, (pairsAtDistance A d : ℝ) ≥ f n * n := by
  sorry

end Erdos605
