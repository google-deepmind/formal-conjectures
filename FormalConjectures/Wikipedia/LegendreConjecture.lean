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
# Legendre's conjecture

*References:*
- [Landau Problems Wikipedia Page](https://en.wikipedia.org/wiki/Landau%27s_problems#Twin_prime_conjecture)
- [Legendre Conjecture Wikipedia Page](https://en.wikipedia.org/wiki/Legendre%27s_conjecture)
-/

/--
Does there always exist at least one prime between consecutive perfect squares?
-/
@[category research open, AMS 11]
theorem legendre_conjecture :
    (∀ᵉ (n ≥ 1), ∃ p ∈ Set.Ioo (n^2) ((n+1)^2), Prime p)
      ↔ answer(sorry) := by
  sorry
