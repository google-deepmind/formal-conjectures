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
# Erdős Problem 843

*Reference:* [erdosproblems.com/843](https://www.erdosproblems.com/843)
-/

open Filter

namespace Erdos843

/--
Are the squares Ramsey $2$-complete? That is, is it true that, in any 2-colouring of the square
numbers, every sufficiently large $n\in \mathbb{N}$ can be written as a monochromatic sum of
distinct squares?
-/
@[category research open, AMS 5 11]
theorem erdos_843 :
    answer(sorry) ↔
      ∀ c : ℕ → Fin 2,
        ∀ᶠ N : ℕ in atTop,
          ∃ (s : Finset ℕ) (i : Fin 2),
            (∀ k ∈ s, c (k ^ 2) = i) ∧ s.sum (fun k ↦ k ^ 2) = N := by
  sorry

end Erdos843
