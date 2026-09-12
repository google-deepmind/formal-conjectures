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

import FormalConjecturesUtil

/-!
# Erdős Problem 1154

*Reference:* [erdosproblems.com/1154](https://www.erdosproblems.com/1154)
-/

open MeasureTheory

namespace Erdos1154

/--
Does there exist, for every $\alpha \in [0,1]$, a ring or field in $\mathbb{R}$ with Hausdorff
dimension $\alpha$?
-/
@[category research open, AMS 11 28]
theorem erdos_1154 :
    answer(sorry) ↔
      ∀ α ∈ Set.Icc (0 : ℝ) 1,
        (∃ R : Subring ℝ, dimH (R : Set ℝ) = ENNReal.ofReal α) ∨
          ∃ F : Subfield ℝ, dimH (F : Set ℝ) = ENNReal.ofReal α := by
  sorry

end Erdos1154
