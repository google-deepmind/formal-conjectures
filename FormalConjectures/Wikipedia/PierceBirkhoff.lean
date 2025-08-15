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
# Pierce–Birkhoff conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Pierce%E2%80%93Birkhoff_conjecture)

The Pierce-Birkhoff conjecture asserts that any piecewise-polynomial function can be expressed
as a maximum of finite minima of finite collections of polynomials. It was first stated in 1956
by Garrett Birkhoff and Richard S. Pierce, though the modern rigorous formulation is due to
Melvin Henriksen and John R. Isbell.

The conjecture has been proved for `n = 1` and `n = 2` by Louis Mahé.
-/

/--
A set is semi-algebraic in `ℝⁿ` if it can be described by a finite union of sets defined by
of multivariate polynomial equations and inequalities.
-/
def IsSemiAlgebraic {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (ι : Type) (p : ι → MvPolynomial (Fin n) ℝ), Finite ι ∧
    S = {x | ∃ i, MvPolynomial.eval x (p i) = 0} ∪ {x | ∃ i, MvPolynomial.eval x (p i) > 0}

/--
A set is semi-algebraic in `ℝ` if it can be described by a finite boolean combination
of polynomial equations and inequalities.
-/
def IsSemiAlgebraic₁ (S : Set ℝ) : Prop :=
  ∃ (ι : Type) (p : ι → Polynomial ℝ), Finite ι ∧
    S = {x | ∃ (i : ι), Polynomial.eval x (p i) = 0} ∪
    {x | ∃ (i : ι), Polynomial.eval x (p i) > 0}



open scoped Polynomial

/--
A function `f : ℝⁿ → ℝ` is piecewise polynomial if there exists a finite covering of `ℝⁿ` by
closed semi-algebraic sets such that the restriction of `f` to each set in the covering is
polynomial.
-/
def IsPiecewiseMvPolynomial {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ (ι : Type) (P : ι → Set (EuclideanSpace ℝ (Fin n)))
    (g : ι → MvPolynomial (Fin n) ℝ),
    Finite ι ∧
    (∀ i, IsClosed (P i)) ∧
    (∀ i, IsSemiAlgebraic (P i)) ∧
    (⋃ i, P i) = Set.univ ∧
    ∀ᵉ (i : ι) (x ∈ P i), f x = MvPolynomial.eval x (g i)

/--
A function `f : ℝ → ℝ` is piecewise polynomial if there exists a finite covering of `ℝ` by
closed semi-algebraic sets such that the restriction of `f` to each set in the covering is
polynomial.
-/
def IsPiecewisePolynomial (f : ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (P : ι → Set ℝ)
    (g : ι → Polynomial ℝ),
    Finite ι ∧
    (∀ (i : ι), IsClosed (P i)) ∧
    (∀ (i : ι), IsSemiAlgebraic₁ (P i)) ∧
    (⋃ (i : ι), P i) = Set.univ ∧
    ∀ᵉ (i : ι) (x ∈ P i), f x = Polynomial.eval x (g i)

/--
The Pierce-Birkhoff conjecture states that for every real piecewise-polynomial function
`f : ℝⁿ → ℝ`, there exists a finite set of polynomials `gᵢⱼ ∈ ℝ[x₁, ..., xₙ]` such that
`f = supᵢ infⱼ(gᵢⱼ)`.
-/
@[category research open, AMS 13]
theorem pierce_birkhoff_conjecture {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPiecewiseMvPolynomial f) :
    ∃ (ι κ : Type) (hι : Fintype ι) (hκ : Fintype κ)
      (g : ι → κ → MvPolynomial (Fin n) ℝ),
      ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (g i j) := by
  sorry

/--
The Pierce-Birkhoff conjecture holds for `n = 1`.
This was proved by Louis Mahé.
-/
@[category research solved, AMS 13]
theorem pierce_birkhoff_conjecture_dim_one (f : ℝ → ℝ)
    (hf : IsPiecewisePolynomial f) :
    ∃ (ι κ : Type) (hι : Fintype ι) (hκ : Fintype κ)
      (g : ι → κ → Polynomial ℝ),
      ∀ x, f x = ⨆ i, ⨅ j, Polynomial.eval x (g i j) := by
  sorry

/--
The Pierce-Birkhoff conjecture holds for `n = 2`.
This was proved by Louis Mahé.
-/
@[category research solved, AMS 13]
theorem pierce_birkhoff_conjecture_dim_two
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : IsPiecewiseMvPolynomial f) :
    ∃ (ι κ : Type) (hι : Fintype ι) (hκ : Fintype κ)
      (g : ι → κ → MvPolynomial (Fin 2) ℝ),
      ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (g i j) := by
  sorry
