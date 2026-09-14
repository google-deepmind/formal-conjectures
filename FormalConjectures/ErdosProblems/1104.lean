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
import FormalConjecturesUtil

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
$$
(1 - o(1)) \sqrt{\frac{n}{\log n}} \le f(n),
$$
where $f(n)$ denotes the maximum chromatic number of a triangle-free graph on
$n$ vertices, formalized as `triangleFreeMaxChromatic n`.
-/
@[category research solved, AMS 5]
theorem erdos_1104.variants.lower :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ))
        ≤ (triangleFreeMaxChromatic n : ℝ) := by
  sorry

/--
Upper bound (Davies–Illingworth 2022).
$$
f(n) \le (2 + o(1)) \sqrt{\frac{n}{\log n}},
$$
where $f(n)$ denotes the maximum chromatic number of a triangle-free graph on
$n$ vertices, formalized as `triangleFreeMaxChromatic n`.
-/
@[category research solved, AMS 5]
theorem erdos_1104.variants.upper :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (triangleFreeMaxChromatic n : ℝ)
        ≤ (2 + ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  sorry

end Erdos1104
