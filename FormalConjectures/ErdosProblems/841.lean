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
# Erdős Problem 841

*Reference:* [erdosproblems.com/841](https://www.erdosproblems.com/841)
-/

open Set

namespace Erdos841

/-- $t_n$ is minimal such that $\{n+1,\ldots,n+t_n\}$ contains a subset whose product with $n$ is
a square (and $t_n=0$ if $n$ is itself a square). -/
noncomputable def t (n : ℕ) : ℕ :=
  sInf { m | ∃ s : Finset ℕ, ↑s ⊆ Icc (n + 1) (n + m) ∧ ∃ k, n * s.prod id = k ^ 2 }

/--
Let $t_n$ be minimal such that $\{n+1,\ldots,n+t_n\}$ contains a subset whose product with $n$ is a
square number (and let $t_n=0$ if $n$ is itself square). Estimate $t_n$.
-/
@[category research open, AMS 11]
theorem erdos_841.lower_bound : answer(sorry) ≤ t := by
  sorry

/-- An upper estimate for $t_n$. -/
@[category research open, AMS 11]
theorem erdos_841.upper_bound : t ≤ answer(sorry) := by
  sorry

end Erdos841
