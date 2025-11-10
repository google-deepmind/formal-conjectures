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

import FormalConjectures.Util.ProblemImports

/-!
# Kummer–Vandiver conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Kummer%E2%80%93Vandiver_conjecture)
-/

open NumberField CyclotomicField IsCyclotomicExtension

-- TODO(Paul-Lez): change `PNat` to `Nat` once the version of Mathlib we're on allows it.

/--
Kummer–Vandiver conjecture states that for every prime $p$, the class number of the maximal
real subfield of $\mathbb{Q}(\zeta_p)$ is not divisible by $p$.
--/
@[category research open, AMS 11]
theorem kummer_vandiver (p : ℕ+) (hp : p.Prime) :
    ¬ ↑p ∣ (classNumber (maximalRealSubfield (CyclotomicField p ℚ))) := by
  sorry
