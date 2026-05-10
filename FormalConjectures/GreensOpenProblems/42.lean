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
# Green's Open Problem 42

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.42)
- [CoEl03] Cohn, Henry, and Noam Elkies. "New upper bounds on sphere packings I."
  Annals of Mathematics (2003): 689-714.
- [Vi17] Viazovska, Maryna S. "The sphere packing problem in dimension 8."
  Annals of mathematics (2017): 991-1015.
- [CKM17] Cohn, H., Kumar, A., Miller, S., Radchenko, D., & Viazovska, M. (2017).
  The sphere packing problem in dimension 24. Annals of mathematics, 185(3), 1017-1033.
- [Sa21] Sardari, Naser Talebizadeh. "Higher Fourier interpolation on the plane."
  arXiv preprint arXiv:2102.08753 (2021).

-/

open Real Complex MeasureTheory
open scoped FourierTransform

namespace Green42

abbrev R1 := EuclideanSpace ℝ (Fin 1)
abbrev R2 := EuclideanSpace ℝ (Fin 2)
abbrev R8 := EuclideanSpace ℝ (Fin 8)
abbrev R24 := EuclideanSpace ℝ (Fin 24)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasureSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The real-valued Fourier transform used in the Cohn--Elkies conditions.
For real radial admissible functions, the complex Fourier transform is expected
to be real-valued; we take `.re` to expose the real scalar used in the inequality. -/
noncomputable def fHat (f : V → ℝ) (t : V) : ℝ :=
  (𝓕 (fun x ↦ (f x : ℂ)) t).re

/--
Definition 2.1 from [CoEl03]: A function is admissible if both the function and its Fourier
transform decay sufficiently fast.
-/
def CohnElkiesAdmissible (f : V → ℝ) : Prop :=
  ∃ C > 0, ∃ δ > 0,
    (∀ x : V, |f x| ≤ C / (1 + ‖x‖) ^ ((Module.finrank ℝ V : ℝ) + δ)) ∧
    (∀ t : V, |fHat f t| ≤ C / (1 + ‖t‖) ^ ((Module.finrank ℝ V : ℝ) + δ))

/--
The structural rules a function must satisfy to successfully pass through
the Cohn-Elkies scheme and generate *some* valid upper bound.
-/
def SatisfiesCohnElkiesScheme (f : V → ℝ) : Prop :=
  CohnElkiesAdmissible f ∧
  (∀ x y : V, ‖x‖ = ‖y‖ → f x = f y) ∧ -- Radial symmetry
  (∀ x : V, 2 ≤ ‖x‖ → f x ≤ 0) ∧       -- Spatial constraint (minimum distance 2)
  (∀ t : V, 0 ≤ fHat f t) ∧            -- Frequency positivity
  (0 < fHat f 0)                       -- Non-zero frequency at the origin

/--
Can the Cohn-Elkies scheme be used to prove the optimal bound for circle-packings in 2 dimensions?
-/
@[category research open, AMS 51 52]
theorem green_42 :
    answer(sorry) ↔ ∃ f : R2 → ℝ,
      SatisfiesCohnElkiesScheme f ∧
      -- Achieves optimal center density for the 2D hexagonal lattice
      f 0 / fHat f 0 = Real.sqrt 3 / 6 := by
  sorry

/-- [CoEl03] proved this when $d = 1$. -/
@[category research solved, AMS 51 52]
theorem green_42.variants.dimension_one :
    ∃ f : R1 → ℝ,
      SatisfiesCohnElkiesScheme f ∧
      -- Achieves optimal center density for the 1D lattice
      f 0 / fHat f 0 = 1 / 2 := by
  sorry

/-- [Vi17] established the case $d = 8$. -/
@[category research solved, AMS 51 52]
theorem green_42.variants.dimension_eight :
    ∃ f : R8 → ℝ,
      SatisfiesCohnElkiesScheme f ∧
      -- Achieves optimal center density for the E8 lattice
      f 0 / fHat f 0 = 1 / 16 := by
  sorry

/-- In [CKM17], [Vi17] was adapted to $d = 24$. -/
@[category research solved, AMS 51 52]
theorem green_42.variants.dimension_twenty_four :
    ∃ f : R24 → ℝ,
      SatisfiesCohnElkiesScheme f ∧
      -- Achieves optimal center density for the Leech lattice
      f 0 / fHat f 0 = 1 := by
  sorry

end Green42
