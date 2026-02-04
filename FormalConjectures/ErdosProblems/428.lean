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
# Erdős Problem 428

*Reference:* [erdosproblems.com/428](https://www.erdosproblems.com/428)
-/

open Nat Filter Set

namespace Erdos428

/--
The density ratio of set $A$ up to $n$ relative to the prime counting function $\pi(n)$.
-/
noncomputable def primeDensityRatio (A : Set ℕ) (n : ℕ) : ℝ :=
  (A ∩ Icc 1 n).ncard / (primeCounting n)

/--
Is there a set $A\subseteq \mathbb{N}$ such that, for infinitely many $n$, all of $n-a$
are prime for all $a\in A$ with $0 < a < n$ and \[\liminf\frac{\lvert A\cap [1,x]\rvert}{\pi(x)}>0?\]
-/
@[category research open, AMS 11]
theorem erdos_428 :
    answer(sorry) ↔ ∃ A : Set ℕ,
      (∃ᶠ n in atTop, ∀ a ∈ A, 0 < a → a < n → (n - a).Prime) ∧
      liminf (fun n ↦ primeDensityRatio A n) atTop > 0 := by
  sorry

end Erdos428
