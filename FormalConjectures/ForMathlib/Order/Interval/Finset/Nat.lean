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

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Card

@[simp]
theorem Nat.ncard_Iio (b : ℕ) : (Set.Iio b).ncard = b := by
  rw [← Finset.coe_Iio, Set.ncard_coe_Finset]
  exact Nat.card_Iio _
