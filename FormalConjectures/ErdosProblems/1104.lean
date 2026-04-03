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
# Erdős Problem 1104

*Reference:* https://www.erdosproblems.com/1104
-/

namespace Erdos1104

open Filter SimpleGraph
open scoped Real

/-- Maximum chromatic number of a triangle-free graph on `n` vertices. -/
noncomputable def triangleFreeMaxChromatic (n : ℕ) : ℕ :=
  sSup {χ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ}

-- TODO: Add erdos_1104.

/--
Lower bound (Hefty–Horn–King–Pfender 2025).
There exists a constant $c_1 \in (0,1]$ such that, for sufficiently large $n$,
$$
c_1 \sqrt{\frac{n}{\log n}} \le f(n),
$$
where $f(n)$ denotes the maximum chromatic number of a triangle-free graph on
$n$ vertices, formalized as `triangleFreeMaxChromatic n`.
-/
@[category research solved, AMS 5]
theorem erdos_1104.variants.lower :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧
      (∀ᶠ n : ℕ in atTop,
        c₁ * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ))
          ≤ (triangleFreeMaxChromatic n : ℝ)) := by
  sorry

/--
Upper bound (Davies–Illingworth 2022).
There exists a constant $c_2 \ge 2$ such that, for sufficiently large $n$,
$$
f(n) \le c_2 \sqrt{\frac{n}{\log n}},
$$
where $f(n)$ denotes the maximum chromatic number of a triangle-free graph on
$n$ vertices, formalized as `triangleFreeMaxChromatic n`.
-/
@[category research solved, AMS 5]
theorem erdos_1104.variants.upper :
    ∃ c₂ : ℝ, 2 ≤ c₂ ∧
      (∀ᶠ n : ℕ in atTop,
        (triangleFreeMaxChromatic n : ℝ)
          ≤ c₂ * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ))) := by
  sorry

end Erdos1104
