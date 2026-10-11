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
module

public import Mathlib.Data.Nat.MaxPrimeFac

@[expose] public section

namespace Nat

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p := by
  exact le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. -/
lemma isLeast_maxPrimeFac {n : ℕ} (hn : 1 < n) :
    IsLeast (upperBounds {p : ℕ | p.Prime ∧ p ∣ n}) (maxPrimeFac n) :=
  isLUB_maxPrimeFac hn

end Nat
