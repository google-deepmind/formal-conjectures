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
# Erdős Problem 387

*Reference:* [erdosproblems.com/387](https://www.erdosproblems.com/387)
-/

open scoped Nat

namespace Erdos387

/--
Is there an absolute constant `c > 0` such that, for all `1 ≤ k < n`, the binomial coefficient
`choose n k` has a divisor in `(cn, n]`?
-/
@[category research open, AMS 11]
theorem erdos_387 : answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n, ∀ k : Finset.Ico (α := ℕ) 1 n,
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (α := ℝ) (c * n) n ∧ d ∣ n.choose k := by
  sorry

end Erdos387
