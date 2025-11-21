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
# Erdős Problem 887

*Reference:* [erdosproblems.com/887](https://www.erdosproblems.com/887)
-/

noncomputable section

open Nat Filter

namespace Erdos887

/--
The count of divisors of `n` that fall inside
the interval $(n^{1/2}, n^{1/2} + C n^{1/4})$.
-/
def divisorsCount (n : ℕ) (C : ℝ) : ℕ :=
  ((divisors n).filter (fun d =>
    n.sqrt < d ∧ d < n.sqrt + C * n ^ (1/4 : ℝ))).card

/--
Is there an absolute constant $K$ such that,
for every $C>0$, if $n$ is sufficiently large
then $n$ has at most $K$ divisors in $(n^{1/2},n^{1/2}+C n^{1/4})$.
-/
@[category research open, AMS 11]
theorem erdos_887 :
  ∃ K : ℕ, ∀ C : ℝ, 0 < C → ∀ᶠ n in atTop, divisorsCount n C ≤ K
    ↔ answer(sorry) := by
  sorry

end Erdos887

end
