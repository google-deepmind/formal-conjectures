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

import FormalConjectures.Util.ProblemImports

open Nat Filter Finset

/-- Predicate for a natural number having only odd digits in base 10. -/
def only_odd_digits (n : ℕ) : Prop :=
  (Nat.digits 10 n).all (fun d => d % 2 = 1)

-- This predicate is computationally decidable. We use a noncomputable instance via Classical.
noncomputable instance only_odd_digits_decidable (n : ℕ) : Decidable (only_odd_digits n) := Classical.propDecidable _

/-- The property defining terms of A347475: $k$ and $T(k) = k(k+1)/2$ have only odd digits. -/
def is_A347475_term (k : ℕ) : Prop :=
  k > 0 ∧ only_odd_digits k ∧ only_odd_digits (k * (k + 1) / 2)

-- This predicate is also decidable.
noncomputable instance is_A347475_term_decidable (k : ℕ) : Decidable (is_A347475_term k) := Classical.propDecidable _

/-- A355276: The number of $L$-digit terms in A347475. -/
noncomputable def A355276 (L : ℕ) : ℕ :=
  if L = 0 then 0 else
  (Finset.filter is_A347475_term (Ico (10^(L - 1)) (10^L))).card

/--
**oeis_347475_conjecture_0**:
Can it be proved that the number of L-digit terms (cf. A355276) tends to infinity as L $\to$ $\infty$?
-/
theorem oeis_347475_conjecture_0 :
  Tendsto A355276 atTop atTop :=
by sorry
