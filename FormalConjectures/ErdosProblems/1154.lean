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
# Erdős Problem 1154

*Reference:* [erdosproblems.com/1154](https://www.erdosproblems.com/1154)

Does there exist, for every α ∈ [0,1], a subring of ℝ with Hausdorff dimension α?

[Er79h] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. 52 (1979), p. 119.

[Va99] Varga, R.S., _Scientific Computation on Mathematical Problems and Conjectures_, 1999.
-/

open MeasureTheory

namespace Erdos1154

/--
Erdős Problem #1154 [Er79h, p.119]:

Does there exist, for every $\alpha \in [0,1]$, a subring of $\mathbb{R}$ with Hausdorff
dimension $\alpha$?

Erdős and Volkmann proved the analogous result for subgroups of $\mathbb{R}$.
Falconer showed that any subring with Hausdorff dimension $\alpha \in (1/2,1)$ cannot be
Borel or Suslin. Edgar and Miller proved that any Borel or analytic subring of $\mathbb{R}$
either has Hausdorff dimension $0$ or equals $\mathbb{R}$. Mauldin proved the result for
subfields assuming the continuum hypothesis.
-/
@[category research open, AMS 13 28]
theorem erdos_1154 : answer(sorry) ↔
    ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
      ∃ S : Subring ℝ, dimH (↑S : Set ℝ) = ENNReal.ofReal α := by
  sorry

end Erdos1154
