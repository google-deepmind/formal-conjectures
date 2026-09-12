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
# Erdős Problem 462

*Reference:* [erdosproblems.com/462](https://www.erdosproblems.com/462)
-/

namespace Erdos462

open Filter
open scoped BigOperators

/--
Let $p(n)$ denote the least prime factor of $n$. Is there a constant $C>0$ such that
$$\sum_{x\leq n\leq x+C\sqrt{x}(\log x)^2}\frac{p(n)}{n}\gg 1$$
for all sufficiently large $x$?
-/
@[category research open, AMS 11]
theorem erdos_462 : answer(sorry) ↔
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c ≤ ∑ n ∈ Finset.Icc x
        ⌊(x : ℝ) + C * Real.sqrt x * (Real.log x) ^ 2⌋₊, (n.minFac : ℝ) / n := by
  sorry

end Erdos462
