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
# Erdős Problem 244

*Reference:* [erdosproblems.com/244](https://www.erdosproblems.com/244)
-/
/-- Let $C > 1$. Does the set of integers of the form $p + \lfloor C^k \rfloor$,
for some prime $p$ and $k\geq 0$, have density $>0$? -/
@[category research open, AMS 11]
theorem erdos_244 : (∀ C > (1 : ℝ), 0 < { p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) }.lowerDensity) ↔
    answer(sorry) := by
  sorry

/-- Romanoff [Ro34] proved that the answer is yes if $C$ is an integer.

[Ro34] Romanoff, N. P., _Über einige Sätze der additiven Zahlentheorie_.
Math. Ann. (1934), 668-678.-/
@[category research solved, AMS 11]
theorem erdos_244.variants.Romanoff {C : ℕ} (hC : 1 < C) :
    0 < { p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) }.lowerDensity := by
  sorry
