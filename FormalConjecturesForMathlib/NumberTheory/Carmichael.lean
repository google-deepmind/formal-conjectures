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

public import Mathlib.NumberTheory.FermatPsp
public import FormalConjecturesForMathlib.Data.Nat.Prime.Composite

open scoped Nat

@[expose] public section

/-!
# Carmichael Numbers

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Carmichael_number)
-/

/--
A Carmichael number is a composite number `n` such that for all `b ≥ 1`,
we have `b^n ≡ b (mod n)`.
-/
def IsCarmichael (n : ℕ) : Prop :=
  Nat.Composite n ∧ ∀ b : ℕ, n ∣ b ^ n - b
