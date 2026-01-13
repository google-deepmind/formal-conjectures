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
# Erdős Problem 260

*Reference:* [erdosproblems.com/260](https://www.erdosproblems.com/260)
-/

namespace Erdos260

open Filter SummationFilter

def an_div_n_tendsto_infinity (an : ℕ → ℝ) : Prop :=
    Tendsto (fun n => an n / (n : ℝ)) atTop atTop

noncomputable def sum_of_sequence (an : ℕ → ℝ) : ℝ :=
∑'[conditional ℕ] n, (an n / 2 ^ (an n))

@[category research open, AMS 11]
theorem erdos_260 (a : ℕ → ℝ) (h : StrictMono a) (h2 : an_div_n_tendsto_infinity a) :
    Irrational (sum_of_sequence a) := by sorry

end Erdos260
