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

import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! # Standard real valued constants

This file is for storing the definition of standard real constants that arise in conjectures.

-/

open Real

/--
**Gompertz constant**
$$\delta = -e * \int_1^∞ e^{-t}/t dt \approx 0.59634$$
-/
noncomputable def gompertzConstant : ℝ :=
  -exp 1 * ∫ (t:ℝ) in Set.Ioi 1, exp (-t) / t

/--
**Catalan's constant**
$$G = \sum_{n=0}^∞ (-1)^n / (2n + 1)^2 \approx 0.91596$$
-/
noncomputable def catalanConstant : ℝ :=
  ∑' n : ℕ, (-1)^n / (2*n + 1)^2
