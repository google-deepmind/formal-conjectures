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

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Bertrand

lemma Nat.exists_prime_not_dvd (n : ℕ) (hn : n ≠ 0) : ∃ p, p.Prime ∧ ¬p ∣ n := by
  let ⟨p, hp, h_lt, _⟩ := exists_prime_lt_and_le_two_mul n hn
  exact ⟨p, hp, not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) h_lt⟩
