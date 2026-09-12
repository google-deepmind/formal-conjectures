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
# Erdős Problem 1134

*Reference:* [erdosproblems.com/1134](https://www.erdosproblems.com/1134)
-/

open Filter Set
open scoped Topology

namespace Erdos1134

/-- The smallest set of naturals containing `1` and closed under `x ↦ 2x+1`, `x ↦ 3x+1`, and
`x ↦ 6x+1`. -/
inductive MemA : ℕ → Prop
  | one : MemA 1
  | two {x} : MemA x → MemA (2 * x + 1)
  | three {x} : MemA x → MemA (3 * x + 1)
  | six {x} : MemA x → MemA (6 * x + 1)

def A : Set ℕ := { n | MemA n }

/--
Let $A\subseteq \mathbb{N}$ be the smallest set which contains $1$ and is closed under the
operations
$$
x\mapsto 2x+1,
$$
$$
x\mapsto 3x+1,
$$
and
$$
x\mapsto 6x+1.
$$
Does $A$ have positive lower density?
-/
@[category research open, AMS 11]
theorem erdos_1134 :
    answer(sorry) ↔ 0 < liminf (fun n : ℕ ↦ ((A ∩ Icc 1 n).ncard : ℝ) / n) := by
  sorry

end Erdos1134
