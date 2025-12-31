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
 - [Tao25] Tao, Terence. Sublevel Sets of Logarithmic Potentials. Terry Tao’s Blog, Dec. 2025
  (https://terrytao.wordpress.com/wp-content/uploads/2025/12/erdos-1038-1.pdf)
-/

open scoped Real ENNReal
open MeasureTheory

namespace Erdos1038

/-- What is the infimum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]`? -/
@[category research open, AMS 28]
theorem erdos_1038.inf (n : ℕ) : answer(sorry) =
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  sorry

/-- The infimum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]` is `< 1.835`. -/
@[category research solved, AMS 28]
theorem erdos_1038.inf_upperBound (n : ℕ) : ⨅ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} < 1.835 := by
  sorry

/-- The infimum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]` is `≥ 2 ^ (4 / 3) - 1`. -/
@[category research solved, AMS 28]
theorem erdos_1038.inf_lowerBound (n : ℕ) : 2 ^ (4 / 3 : ℝ) - 1 ≤ ⨅ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  sorry

/-- The supremum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]` is  `2 * 2 ^ (1 / 2)`. This is proved in
[Tao25]. -/
@[category research solved, AMS 28]
theorem erdos_1038.sup (n : ℕ) : 2 * 2 ^ (1 / 2 : ℝ) =
    ⨆ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  sorry

end Erdos1038
