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
  ext m
  simp
  refine ⟨fun ⟨x, hx, hxm⟩ => ?_, fun ⟨hm, hmn⟩ => ⟨m / 2, ?_, ?_⟩⟩
  · simp [← hxm]
    omega
  · rwa [← mul_lt_mul_left (show 0 < 2 by norm_num),
      Nat.mul_div_cancel' (by exact even_iff_two_dvd.mp hm),
      Nat.mul_div_cancel' (by exact even_iff_two_dvd.mp h)]
  · rw [Nat.mul_div_cancel' (by exact even_iff_two_dvd.mp hm)]

theorem Nat.image_mul_two_Iio (n : ℕ) :
    (2 * ·) '' Set.Iio ((n + 1) / 2) = { n | Even n } ∩ Set.Iio n := by
  ext m
  simp
  refine ⟨fun ⟨x, hx, hxm⟩ => ?_, fun ⟨hm, hmn⟩ => ⟨m / 2, ⟨by omega, ?_⟩⟩⟩
  · simp [← hxm]
    omega
  · rw [Nat.mul_div_cancel' (by exact even_iff_two_dvd.mp hm)]
