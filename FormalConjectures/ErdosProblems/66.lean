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

import FormalConjecturesUtil

/-!
# Erdős Problem 66

*Reference:* [erdosproblems.com/66](https://www.erdosproblems.com/66)
-/


namespace Erdos66

open Filter AdditiveCombinatorics
open scoped Topology

/--
Is there and $A \subset \mathbb{N}$ is such that
$$\lim_{n\to \infty}\frac{1_A\ast 1_A(n)}{\log n}$$
exists and is $\ne 0$?
-/
@[category research open, AMS 11]
theorem erdos_66 : answer(sorry) ↔ ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
    Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  sorry

-- TODO(firsching): add the theorems/conjectures for the comments on the page

end Erdos66
