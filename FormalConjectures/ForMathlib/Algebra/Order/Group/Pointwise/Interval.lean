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

import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Tactic

theorem Nat.image_mul_two_Iio_even {n : ℕ} (h : Even n) :
    (2 * ·) '' Set.Iio (n / 2) = { n | Even n } ∩ Set.Iio n := by
  norm_num [Set.ext_iff, Nat.even_iff] at *
  use ⟨by omega, fun _ =>⟨. / 2, by omega⟩⟩

theorem Nat.image_mul_two_Iio (n : ℕ) :
    (2 * ·) '' Set.Iio ((n + 1) / 2) = { n | Even n } ∩ Set.Iio n := by
  norm_num [Nat.lt_iff_add_one_le, Set.ext_iff, Nat.le_div_iff_mul_le,
    Nat.even_iff]
  use ⟨by omega, fun _ => ⟨. / 2, by omega⟩⟩
