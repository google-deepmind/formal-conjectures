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
# Tao's Optimization Constant 29 / Kissing number in dimension 5

*References:*
- [Tao's Optimization Constant 29](https://teorth.github.io/optimizationproblems/constants/29a.html)
- [KZ1873] Korkine, A.; Zolotareff, G., *Sur les formes quadratiques*.
  Math. Ann. 6 (1873), 366–389.
- [CR2024] Cohn, H.; Rajagopal, S., *A modular design for optimal five-dimensional
  kissing configurations*. [arXiv:2412.00937](https://arxiv.org/abs/2412.00937).
- [Cox1963] Coxeter, H. S. M., *An upper bound for the number of equal nonoverlapping
  spheres that can touch another of the same size*. Proc. Sympos. Pure Math. 7 (1963), 53–71.
- [BV2008] Bachoc, C.; Vallentin, F., *New upper bounds for kissing numbers from
  semidefinite programming*. [Paper](https://ir.cwi.nl/pub/12655/12655D.pdf) (2008).
- [MV2009] Mittelmann, H. D.; Vallentin, F., *High-accuracy semidefinite programming
  bounds for kissing numbers*. [arXiv:0902.1105](https://arxiv.org/abs/0902.1105).
-/

namespace Constant29

/-- Unit vectors representing mutually nonoverlapping spheres tangent to a central sphere.
Note this translates to the usual formulation via spheres. -/
def IsKissingConfiguration {n : ℕ} (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ x ∈ A, ‖x‖ = 1) ∧ ∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y ≤ 1 / 2

/-- A subset of a kissing configuration is a kissing configuration. -/
@[category API, AMS 52]
theorem IsKissingConfiguration.mono {n : ℕ} {A B : Finset (EuclideanSpace ℝ (Fin n))}
    (hB : IsKissingConfiguration B) (hAB : A ⊆ B) : IsKissingConfiguration A :=
  ⟨fun x hx ↦ hB.1 x (hAB hx), fun x hx y hy hxy ↦ hB.2 x (hAB hx) y (hAB hy) hxy⟩

/-- The kissing number in $n$ dimensions. -/
noncomputable def KissingNumer (n : ℕ) :=
  sSup (Finset.card '' {A | IsKissingConfiguration (n := n) A})

/-- **Tao's Optimization Constant 29 / Kissing number in dimension 5**. -/
noncomputable def C29 : ℕ := KissingNumer 5

/-- A lower bound supplied by the ten vertices of a cross polytope [CR2024]. -/
@[category textbook, AMS 52]
theorem c29_ge_10 : 10 ≤ C29 := by
  sorry

/-- The current best known lower bound [KZ1873; CR2024], supplied by the normalized
roots of the $D_5$ lattice. -/
@[category research solved, AMS 52]
theorem c29_lower_bound : 40 ≤ C29 := by
  sorry

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 52]
theorem c29_lower_bound_improved : answer(sorry) ↔ 40 < C29 := by
  sorry

/-- The first known upper bound [Cox1963], obtained from spherical geometry. -/
@[category research solved, AMS 52]
theorem c29_le_48 : C29 ≤ 48 := by
  sorry

/-- An intermediate upper bound [BV2008], obtained by semidefinite programming
for spherical codes. -/
@[category research solved, AMS 52]
theorem c29_le_45 : C29 ≤ 45 := by
  sorry

/-- The current best known upper bound [MV2009], obtained by high-accuracy
semidefinite programming and the integrality of the kissing number. -/
@[category research solved, AMS 52]
theorem c29_upper_bound : C29 ≤ 44 := by
  sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 52]
theorem c29_upper_bound_improved : answer(sorry) ↔ C29 < 44 := by
  sorry

end Constant29
