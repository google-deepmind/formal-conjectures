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
# Erdős Problem 1201

*Reference:* [erdosproblems.com/1201](https://www.erdosproblems.com/1201)
-/

open Nat Filter Finset
open Classical

namespace Erdos1201

/--
The set of $n$ for which $P(n(n+1)\cdots(n+k)) > n^{1-\epsilon}$, where $P(m)$ is the greatest prime
divisor of $m$.
-/
noncomputable def Erdos1201Set (ε : ℝ) (k : ℕ) : Set ℕ :=
  { n : ℕ |
    ((sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ range (k + 1), (n + i)} : ℕ) : ℝ) > (n : ℝ) ^ (1 - ε) }

/--
Is it true that for every $\epsilon,\eta>0$ there exists a $k$ such that the density of $n$
for which $P(n(n+1)\cdots(n+k))>n^{1-\epsilon}$ is at least $1-\eta$ (where $P(m)$ is the greatest
prime divisor of $m$)?
-/
@[category research open, AMS 11]
theorem erdos_1201 :
    answer(sorry) ↔
      ∀ ε > 0, ∀ η > 0, ∃ k : ℕ,
        atTop.liminf (fun x : ℕ ↦
          (((count (Erdos1201Set ε k) x : ℝ) / (x : ℝ)) : EReal)) ≥ (1 - η : EReal) := by
  sorry

/--
Erdős wrote he could prove this for $\epsilon=1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_1201.variants.epsilon_half :
    ∀ η > 0, ∃ k : ℕ,
      atTop.liminf (fun x : ℕ ↦
        (((count (Erdos1201Set (1 / 2 : ℝ) k) x : ℝ) / (x : ℝ)) : EReal)) ≥ (1 - η : EReal) := by
  sorry

end Erdos1201
