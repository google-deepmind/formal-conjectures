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
# Erdős Problem 705

*References:*
- [erdosproblems.com/705](https://www.erdosproblems.com/705)
- [OD99] P. O'Donnell, High girth unit-distance graphs. PhD Dissertation, Rutgers University (1999).
-/

namespace Erdos705

open scoped EuclideanGeometry
open SimpleGraph

/--
Let $G$ be a finite unit distance graph in $\mamthbb{R}^2$.
Is there some $k$ such that if $G$ has girth $≥ k$, then $\chi(G) ≤ 3$?

The general case was solved by O'Donnell [OD99], who constructed finite unit distance graphs with
chromatic number $4$ and arbitrarily large girth.
-/
@[category research solved, AMS 5]
theorem erdos_705:
  answer(False) ↔ ∃ k, ∀ V : Set ℝ², V.Finite →
    (UnitDistancePlaneGraph V).girth ≥ k → (UnitDistancePlaneGraph V).chromaticNumber ≤ 3 := by
  sorry


-- TODO: add statements for the concrete constructions in the additional material

end Erdos705
