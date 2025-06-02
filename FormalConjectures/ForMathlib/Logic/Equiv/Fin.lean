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

import Mathlib.Logic.Equiv.Fin

variable {n : ℕ}

theorem lt_finRotate_of_ne_last {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    i < finRotate _ i := by
  rw [Fin.lt_iff_val_lt_val, coe_finRotate_of_ne_last hi, Nat.lt_add_one_iff]
