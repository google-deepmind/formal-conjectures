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
# Erdős Problem 1181

*Reference:* [erdosproblems.com/1181](https://www.erdosproblems.com/1181)
-/

open Filter Finset Real
open scoped Topology

namespace Erdos1181

/-- $q(n,k)$ is the least prime which does not divide $\prod_{1\leq i\leq k}(n+i)$. -/
noncomputable def q (n k : ℕ) : ℕ :=
  sInf { p : ℕ | p.Prime ∧ ∀ i ∈ Icc 1 k, ¬ p ∣ n + i }

/--
Let $q(n,k)$ denote the least prime which does not divide $\prod_{1\leq i\leq k}(n+i)$. Is it true
that there exists some $c>0$ such that, for all large $n$,
$$
q(n,\log n)<(1-c)(\log n)^2?
$$
-/
@[category research open, AMS 11]
theorem erdos_1181 :
    answer(sorry) ↔
      ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        q n ⌊log n⌋₊ < (1 - c) * (log n) ^ 2 := by
  sorry

end Erdos1181
