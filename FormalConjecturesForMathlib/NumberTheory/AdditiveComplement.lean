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


public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# Additive complements

Two sets of naturals are *additive complements* when their sumset contains every large integer.
-/

open Filter

open scoped Pointwise

/-- `A` and `B` are *additive complements* if `A + B` contains all large integers. -/
def IsAdditiveComplement (A B : Set ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, n ∈ A + B

theorem IsAdditiveComplement.symm {A B : Set ℕ} (h : IsAdditiveComplement A B) :
    IsAdditiveComplement B A := by
  filter_upwards [h] with n hn using by rwa [Set.addCommMonoid.add_comm]
