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

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Sifted positive integers
-/

@[expose] public section

/-- The set of positive integers not divisible by any element of `A`. -/
def sievedSet (A : Set ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬(a ∣ n)}
