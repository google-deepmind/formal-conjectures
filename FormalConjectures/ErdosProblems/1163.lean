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

import FormalConjecturesUtil

/-!
# Erdős Problem 1163

*References:*
- [erdosproblems.com/1163](https://www.erdosproblems.com/1163)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

open Filter

namespace Erdos1163

/-- `f n` counts the number of subgroups of `S_n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/--
The proportion of subgroups of `S_n` whose order is divisible by `m`.
-/
noncomputable def orderDivisibleDensity (n m : ℕ) : ℝ :=
  (Nat.card {H : Subgroup (Equiv.Perm (Fin n)) | m ∣ Nat.card H} : ℝ) / f n

/--
Describe (by statistical means) the arithmetic structure of the orders of subgroups of $S_n$.
-/
@[category research open, AMS 20]
theorem erdos_1163 :
    let p : ℕ → ℝ := answer(sorry)
    ∀ m > 0, Tendsto (fun n : ℕ ↦ orderDivisibleDensity n m) atTop (nhds (p m)) := by
  sorry

end Erdos1163
