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
# Erdős Problem 174

*Reference:* [erdosproblems.com/174](https://www.erdosproblems.com/174)

A finite set $A \subset \mathbb{R}^n$ is called Ramsey if, for any $k \geq 1$, there exists some
$d = d(A,k)$ such that in any $k$-colouring of $\mathbb{R}^d$ there exists a monochromatic
copy of $A$. Characterise the Ramsey sets in $\mathbb{R}^n$.

Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus [EGMRSS73] proved
that every Ramsey set is 'spherical': it lies on the surface of some sphere.
Graham has conjectured that every spherical set is Ramsey, which would give a
complete characterisation.

Known Ramsey sets include vertices of $k$-dimensional rectangles [EGMRSS73],
non-degenerate simplices [FrRo90], trapezoids [Kr92], and regular
polygons/polyhedra [Kr91].

[EGMRSS73] Erdős, P., Graham, R. L., Montgomery, P., Rothschild, B. L., Spencer, J., and
Straus, E. G., _Euclidean Ramsey theorems_, J. Combin. Theory Ser. A, 1973.

[FrRo90] Frankl, P. and Rödl, V., _A partition property of simplices in Euclidean space_,
J. Amer. Math. Soc., 1990.

[Kr91] Kříž, I., _Permutation groups in Euclidean Ramsey theory_, Proc. Amer. Math. Soc., 1991.

[Kr92] Kříž, I., _All trapezoids are Ramsey_, Discrete Math., 1992.
-/

namespace Erdos174

/-- A finite subset $A$ of $\mathbb{R}^n$ is Euclidean Ramsey if for every $k \geq 1$, there
exists $d$ such that any $k$-coloring of $\mathbb{R}^d$ contains a monochromatic
isometric copy of $A$ (i.e., a copy obtained by a distance-preserving map). -/
def IsEuclideanRamsey (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ d : ℕ, ∀ f : EuclideanSpace ℝ (Fin d) → Fin k,
      ∃ φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d),
        (∀ x y, dist (φ x) (φ y) = dist x y) ∧
        ∃ c : Fin k, ∀ a ∈ A, f (φ a) = c

/-- A finite set in $\mathbb{R}^n$ is spherical if all its points lie on the surface
of some sphere (are equidistant from some center point). -/
def IsSpherical (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin n)) (r : ℝ),
    ∀ a ∈ A, dist a center = r

/--
Erdős Problem 174 / Graham's Conjecture:
A finite set $A \subset \mathbb{R}^n$ is Ramsey if and only if it is spherical.

The forward direction (Ramsey $\to$ spherical) was proved by Erdős, Graham,
Montgomery, Rothschild, Spencer, and Straus [EGMRSS73].

The reverse direction (spherical $\to$ Ramsey) is Graham's open conjecture.
-/
@[category research open, AMS 5 52]
theorem erdos_174 :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A ↔ IsSpherical n A := by
  sorry

end Erdos174
