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

/-!
# Erdős Problem 857

*Reference:* [erdosproblems.com/857](https://www.erdosproblems.com/857)

For fixed `n, k`, let `m(n, k)` be minimal such that every family of subsets of `[n]`
of size at least `m(n, k)` contains a `k`-sunflower.
The problem asks to estimate `m(n, k)`, ideally asymptotically.
-/

open Filter

namespace Erdos857

/--
`m(n, k)`: minimal sunflower-forcing family size in the non-uniform `[n]` model.
-/
noncomputable def m (n k : ℕ) : ℕ :=
  sInf {t : ℕ | ∀ (F : Set (Set (Fin n))), t ≤ F.ncard →
    ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/--
Estimate `m(n,k)`, or better give an asymptotic formula.
-/
@[category research open, AMS 5]
theorem erdos_857 :
    let f : ℕ → ℕ → ℝ := answer(sorry)
    ∀ k : ℕ, 3 ≤ k → Tendsto (fun n : ℕ => (m n k : ℝ) / f k n) atTop (nhds 1) := by
  sorry

end Erdos857
