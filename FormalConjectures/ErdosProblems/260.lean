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

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos260

open Filter SummationFilter


/- limit of an/n -> infinity -/
def an_div_n_tendsto_infinity (an : ℕ → ℝ) : Prop :=
/- so the 'function' an/n tends to positive infinity -/
Tendsto (fun n => an n / (n : ℝ)) atTop atTop

/- this defines the infinite sum of the sequence an / (2 ^ (an))-/
noncomputable def sum_of_sequence (an : ℕ → ℝ) : ℝ :=
∑'[conditional ℕ] n, (an n / 2 ^ (an n))

/- check if a sum is rational -/
def sum_is_rational (a : ℕ → ℝ) : Prop := ∃ r : ℚ, (sum_of_sequence a) = (r : ℝ)

/- So a is a function that maps natural to reals this is a(0), a(1), ... a (n) -/
/- then a(n)/n tendsto positive infinity -/
theorem erdos_260 (a : ℕ → ℝ) (h : StrictMono a) (h2 : an_div_n_tendsto_infinity a) :
/- then the sum of a(n)/ 2^(a(n)) is not rational -/
¬ sum_is_rational a := by sorry


end Erdos260
