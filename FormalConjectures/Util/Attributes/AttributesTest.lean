/-
Copyright 2025 Google LLC

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

import FormalConjectures.Util.Attributes
import Mathlib

-- The `Category` and `ProblemSubject` attributes

@[category test]
theorem test : 1 + 1 = 2 := by
  sorry

@[category research solved, AMS 11]
theorem FLT : FermatLastTheorem := by
  sorry

open scoped Real in
@[category research open, AMS 11 33]
theorem an_open_problem : Transcendental ℝ (π + rexp 1) := by
  sorry
