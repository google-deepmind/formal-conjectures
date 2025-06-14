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
# Exponentials conjectures and theorems

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Four_exponentials_conjecture)
- [Wa09] Waldschmidt M. (2009). Variations on the six exponentials Theorem.
-/

open Complex

/--
The space of logarithms of algebraic numbers over ℚ.
-/
def L : Subspace ℚ ℂ := Submodule.span ℚ { x : ℂ | IsAlgebraic ℚ x.exp }

/--
**Algebraic independence of logarithms of algebraic numbers conjecture**
Let $\lambda_i$ be $\mathbb Q$-linearly independent elements of $\mathcal L$,
then $\lambda_i$ are algebraically independent.
-/
@[category research open, AMS 11]
theorem algebraic_independence_conjecture (n : ℕ) (x : Fin n → L) (h: LinearIndependent ℚ x) :
   AlgebraicIndependent ℚ (fun i ↦ (x i : ℂ)) := by
  sorry

/--
**Three exponentials conjecture**
Let $x_0, x_1$ are complex numbers and $\gamma$ a nonzero algebraic number,
then at least one of the following four numbers is transcendental:
$$e^{x_0y},e^{x_1y},e^{\gamma x_1/x_2}$$
-/
@[category research open, AMS 11]
theorem three_exponentials_conjecture (x : Fin 2 → ℂ) (y γ : ℂ) (hγ : γ ≠ 0 ∧ IsAlgebraic ℚ γ) :
    ∃ i : Fin 2, Transcendental ℚ (exp (x i * y)) ∨ Transcendental ℚ (exp (γ * x 1 / x 2)) := by
  sorry

/--
**Four exponentials conjecture**
Let $x_0, x_1$ and $y_0, y_1$ be $\mathbb Q$-linearly independent pairs of complex numbers,
then some $e^{x_i y_j}$ is transcendental.
-/
@[category research open, AMS 33]
theorem four_exponentials_conjecture (x : Fin 2 → ℂ) (y : Fin 2 → ℂ)
  (h1 : LinearIndependent ℚ x) (h2 : LinearIndependent ℚ y) :
    ∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j)) := by
  sorry

/--
**Five exponentials theorem**
Let $x_0, x_1$ and $y_0, y_1$ be $\mathbb Q$-linearly independent pairs of complex numbers,
and $\gamma$ a nonzero algebraic number. Then at least one of the following holds:
1. Some $e^{x_i y_j}$ is transcendental.
2. $e^{\gamma x_1 / x_0}$ is transcendental.
-/
@[category research solved, AMS 33]
theorem five_exponentials_theorem (x : Fin 2 → ℂ) (y : Fin 2 → ℂ) (γ : ℂ) (hγ : γ ≠ 0 ∧ IsAlgebraic ℚ γ)
  (h1 : LinearIndependent ℚ x) (h2 : LinearIndependent ℚ y) :
    (∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j))) ∨ Transcendental ℚ (exp (γ * x 1 / x 0)) := by
  sorry

/--
**Six exponentials theorem**
Let $x_0, x_1, x_2$ and $y_0, y_1$ be $\mathbb Q$-linearly independent tuples of complex numbers,
then some $e^{x_i y_j}$ is transcendental.
-/
@[category research solved, AMS 33]
theorem six_exponentials_theorem (x : Fin 3 → ℂ) (y : Fin 2 → ℂ)
  (h1 : LinearIndependent ℚ x) (h2 : LinearIndependent ℚ y) :
    ∃ i : Fin 3, ∃ j : Fin 2, Transcendental ℚ (exp (x i * y j)) := by
  sorry
