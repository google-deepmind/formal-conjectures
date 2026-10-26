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

public import Mathlib.Probability.Independence.Basic

/-!
# Independent random variables with a common law
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- An indexed family of measurable, independent random variables with the same prescribed law. -/
structure IsIIDWithLaw {ι Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Y : ι → Ω → X) (μ : Measure Ω) (ν : Measure X) : Prop where
  measurable i : Measurable (Y i)
  iIndepFun : iIndepFun Y μ
  map_eq i : Measure.map (Y i) μ = ν

end ProbabilityTheory
