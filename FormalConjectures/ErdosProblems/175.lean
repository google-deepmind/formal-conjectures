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
# Erdős Problem 175

*Reference:* [erdosproblems.com/175](https://www.erdosproblems.com/175)

Sárközy proved the assertion for all sufficiently large `n`; Granville--Ramaré and Velammal
independently proved the full range `n ≥ 5`.
-/

namespace Erdos175

/--
Show that, for any $n\geq 5$, the binomial coefficient $\binom{2n}{n}$ is not squarefree.
-/
@[category research solved, AMS 11]
theorem erdos_175 (n : ℕ) (hn : 5 ≤ n) :
    ¬ Squarefree ((2 * n).choose n) := by
  sorry

end Erdos175
