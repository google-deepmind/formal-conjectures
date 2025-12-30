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
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Erdős Problem 1038

*Reference:*
 - [erdosproblems.com/1038](https://www.erdosproblems.com/1038)
-/

open MeasureTheory

namespace Erdos1038

/-- What is the infimum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` of degree `n`
with `n` roots in `[-1,1]`? -/
@[category research open, AMS 60]
theorem erdos_1038.inf (n : ℕ) : answer(sorry) =
    ⨅ f : {f : Polynomial ℝ // f.IsMonicOfDegree n ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = n},
    volume {x | |f.1.eval x| < 1} := by
  sorry

/-- What is the supremum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` of degree `n`
with `n` roots in `[-1,1]`? -/
@[category research open, AMS 60]
theorem erdos_1038.sup (n : ℕ) : answer(sorry) =
    ⨆ f : {f : Polynomial ℝ // f.IsMonicOfDegree n ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = n},
    volume {x | |f.1.eval x| < 1} := by
  sorry

end Erdos1038
