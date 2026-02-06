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

open Filter

/-
Let $a_1 < a_2 < \cdots$ be an increasing sequence such that
\frac{a_n}{n} \to \infty.
Is the sum
\sum_{n}^{\infty} \frac{a_n}{2^{a_n}} irrational?
-/

@[category research open, AMS 11]
theorem erdos_260 (a : ℕ → ℝ)(s : ℝ)
                  (h : StrictMono a)
                  (h2 : Tendsto (fun n => a n / (n : ℝ)) atTop atTop)
                  (h3 : HasSum (fun n => a n / 2 ^ (a n)) s) :
    Irrational s := by
  sorry

end Erdos260
