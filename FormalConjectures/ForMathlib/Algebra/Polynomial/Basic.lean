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

import Mathlib

open Polynomial

/-!
This file introduces some common assumptions made on polynomials in certain conjectures.
Note that the terminology is non-standard.
-/

/--
**Bunyakovsky condition**
A condition on polynomials in the Schinzel and Bunyakovsky conjectures.
Holds for nonconstant irreducible polynomial with positive leading coefficient.
-/
def BunyakovskyCondition (f : ℤ[X]) : Prop :=
  1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff

/--
**Schinzel condition**
A condition on sets of polynomials in the Schinzel and Bunyakovsky conjectures.
Holds if for every prime $p$ there exists a natural $n$ such that $p$ not divides $f_i(n)$ for all $f_i$.
-/
def SchinzelCondition (fs : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ f ∈ fs, ¬(p : ℤ) ∣ f.eval (n : ℤ)
