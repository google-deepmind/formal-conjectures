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
# Erdős Problem 849

*Reference:* [erdosproblems.com/849](https://www.erdosproblems.com/849)
-/
open Nat

namespace Erdos849

/--
Is it true that, for every integer $t\geq1$, there is some integer $a$ such that ${n \choose k} = a$
with $1\leq k \le \frac{n}{2}$ has exactly $t$ solutions?
-/
@[category research open, AMS 11]
theorem erdos_849 (t : ℕ) (h : t ≥ 1) : ∃ (a : ℕ),
    {n : ℕ | ∃ (k : ℕ), (k ≥ 1) ∧ k ≤ (n : ℝ) / 2 ∧ choose n k = a}.ncard = t ↔ answer(sorry) := by
  sorry

end Erdos849

-- Is it true that, for every integer t≥1, there is some integer a such that
-- (nk)=a
-- (with 1≤k≤n/2) has exactly t solutions?
