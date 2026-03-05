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
# Erdős Problem 260

Let $a_1 < a_2 < \cdots$ be a strictly increasing sequence of natural numbers with
$a_n / n \to \infty$. Is $\sum a_n / 2^{a_n}$ necessarily irrational?

*Reference:* [erdosproblems.com/260](https://www.erdosproblems.com/260)
-/

open Filter

namespace Erdos260

/--
Let $a_1 < a_2 < \cdots$ be a strictly increasing sequence of natural numbers such
that $a_n / n \to \infty$. Is $\sum_n a_n / 2^{a_n}$ irrational?
-/
@[category research open, AMS 11]
theorem erdos_260 : answer(sorry) ↔
    ∀ a : ℕ → ℕ,
      StrictMono a →
      Tendsto (fun n => (a n : ℝ) / (n : ℝ)) atTop atTop →
      Irrational (∑' n, (a n : ℝ) / (2 : ℝ) ^ (a n)) := by
  sorry

end Erdos260
