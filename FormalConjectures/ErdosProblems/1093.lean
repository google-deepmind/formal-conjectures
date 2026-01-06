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
# Erdős Problem 1093

*Reference:* [erdosproblems.com/1093](https://www.erdosproblems.com/1093)
-/

namespace Erdos1093

open Finset Nat

/--
If defined, the deficiency is the count of $0 \le i < k$ such that $n - i$ is $k$-smooth.
-/
noncomputable def deficiency (n k : ℕ) : ℕ :=
  #{i ∈ range k | n - i ∈ smoothNumbers k}

/--
Are there infinitely many binomial coefficients with deficiency 1?
-/
@[category research open, AMS 5]
theorem erdos_1093.parts.i :
    answer(sorry) ↔ {x : ℕ × ℕ | let k := x.1; let n := x.2; k < n ∧ deficiency n k = 1 ∧
      ∀ p, p.Prime → (p ∣ choose n k) → k < p}.Infinite := by
  sorry

/--
Are there only finitely many binomial coefficients with deficiency > 1?
-/
@[category research open, AMS 5]
theorem erdos_1093.parts.ii :
    {x : ℕ × ℕ | let k := x.1; let n := x.2; k < n ∧ deficiency n k > 1 ∧
      ∀ p, p.Prime → (p ∣ choose n k) → k < p}.Finite := by
  sorry

end Erdos1093
