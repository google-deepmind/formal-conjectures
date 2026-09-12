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
# Erdős Problem 1149

*Reference:* [erdosproblems.com/1149](https://www.erdosproblems.com/1149)
-/

open Real Set

namespace Erdos1149

/--
Let $\alpha>0$ be a real number, not an integer. The density of integers $n\geq 1$ for which
$(n,\lfloor n^\alpha\rfloor)=1$ is $6/\pi^2$.
-/
@[category research open, AMS 11]
theorem erdos_1149 (α : ℝ) (hα : 0 < α) (hnint : ∀ n : ℤ, α ≠ n) :
    { n : ℕ | 0 < n ∧ Nat.Coprime n ⌊(n : ℝ) ^ α⌋₊ }.HasDensity (6 / π ^ 2) := by
  sorry

end Erdos1149
