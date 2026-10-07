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


public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The scale `L`

`L n = exp (sqrt (log n * log (log n)))` is the scale that shows up in smooth-number and
covering-system estimates, usually as `n ^ (1 + o(1))` corrections of the form `L n ^ (-1 + o(1))`.
-/

open Real

/-- The scale $L(n)=\exp(\sqrt{\log n\log\log n})$. -/
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))
