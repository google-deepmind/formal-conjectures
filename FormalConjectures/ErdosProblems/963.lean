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
# Erdős Problem 963

*Reference:* [erdosproblems.com/963](https://www.erdosproblems.com/963)
-/

open Finset

namespace Erdos963

/--
Let $f(n)$ be the maximal $k$ such that in any set $A \subseteq \mathbb{R}$ of size $n$ there is a
subset $B \subseteq A$ of size $|B| \ge k$ which is *dissociated*, that is, the sums
$\sum_{b \in S} b$ are distinct for all $S \subseteq B$ (this is `AddDissociated`).

Estimate $f(n)$; in particular, is it true that $f(n) \ge \lfloor \log_2 n \rfloor$?

Formalised here as: for every finite $A \subseteq \mathbb{R}$ there is a dissociated subset
$B \subseteq A$ with $\lfloor \log_2 |A| \rfloor \le |B|$.
-/
@[category research open, AMS 5]
theorem erdos_963 :
    answer(sorry) ↔
      ∀ A : Finset ℝ, ∃ B ⊆ A,
        Nat.log 2 A.card ≤ B.card ∧ AddDissociated (B : Set ℝ) := by
  sorry

end Erdos963
