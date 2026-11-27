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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 908

*References:*
- [erdosproblems.com/908](https://www.erdosproblems.com/908)
-/

@[expose] public section

open Filter Topology MeasureTheory SimpleGraph

namespace Erdos908

/-- If every positive increment of $f$ is measurable, then $f$ is the sum of a continuous
function, an additive function, and a function whose increments vanish almost everywhere
for each fixed translation. Proved by Laczkovich [La80]. -/
@[category research solved, question, AMS 26 39]
theorem erdos_908 (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, 0 < h → Measurable (fun x => f (x + h) - f x)) :
    ∃ g a r : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧
      (∀ h : ℝ, ∀ᵐ x ∂volume, r (x + h) = r x) ∧ f = g + a + r := by
  sorry

end Erdos908
