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

open scoped Manifold

/-!
# Mathoverflow 1973

Does the 6-sphere $S^6$ admit the structure of a complex manifold?

*Reference:* [mathoverflow/1973](https://mathoverflow.net/questions/1973/)
asked by user [*Fetchinson0234*](https://mathoverflow.net/users/41312/victor-ramos)
-/

/-- The unit `n`-sphere, defined as `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (n + 1))`. -/
abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.sphere 0 1

/--
Does the 6-sphere admit a complex structure, i.e. an atlas of holomorphically compatible charts
relating it to `EuclideanSpace ℂ (Fin 3)`?
-/
@[category research open, AMS 32]
theorem mathoverflow_1973 :
    (∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6)) ↔ answer(sorry) := by
  sorry
