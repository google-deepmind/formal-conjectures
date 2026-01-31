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
# Erdős Problem 260

*Reference:* [erdosproblems.com/260](https://www.erdosproblems.com/260)
-/

namespace Erdos260

/--
Let $a_n$ be a sequence such that $\frac{a_n}{n} \to \infty$.
Is the sum $\sum_n \frac{a_n}{2^{a_n}}$ irrational?
-/
@[category research open, AMS 11]
theorem erdos_260 : answer(sorry) ↔ ∀ (a : ℕ → ℕ),
    Filter.Tendsto (fun n => (a n : ℚ) / n) Filter.atTop Filter.atTop →
    Irrational (∑' n : ℕ, (a n : ℚ) / (2 ^ (a n))) := by
  sorry

end Erdos260
