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
# Erdős Problem 488

*Reference:* [erdosproblems.com/488](https://www.erdosproblems.com/488)
-/

open Classical

namespace Erdos488

/--
Let $A$ be a finite set and
$$B=\{ n \geq 1 : a\mid n\textrm{ for some }a\in A\}.$$
Is it true that, for every $m>n\geq \max(A)$,
$$\frac{\lvert B\cap [1,m]\rvert }{m}< 2\frac{\lvert B\cap [1,n]\rvert}{n}?$$
-/
@[category research open, AMS 5 11]
theorem erdos_488 : answer(sorry) ↔ ∀ (A : Finset ℕ), A.Nonempty →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  sorry

end Erdos488
