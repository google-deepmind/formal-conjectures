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
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 341

*Reference:* [erdosproblems.com/341](https://www.erdosproblems.com/341)
-/

open Nat Set Filter
open scoped Topology

namespace Erdos341

/--
Let $A=\{a_1 < \cdots < a_k\}$ be a finite set of integers and extend it to an infinite
sequence $\overline{A}=\{a_1 < a_2 < \cdots \}$ by defining $a_{n+1}$ for $n \geq k$ to be
the least integer exceeding $a_n$ which is not of the form $a_i + a_j$ with $i,j \leq n$.
Is it true that the sequence of differences $a_{m+1}-a_m$ is eventually periodic?

This problem is discussed under Problem 7 on Green's open problems list.
-/
@[category research open, AMS 11]
theorem erdos_341 :
    answer(sorry) ↔
      ∀ (a : ℕ → ℤ),
        (∀ᶠ n in atTop,
          IsLeast { x | a n < x ∧ x ∉ { a i + a j | (i ≤ n) (j ≤ n) } } (a (n + 1))) →
        let d := fun i ↦ a (i + 1) - a i
        ∃ p > 0, ∀ᶠ m in atTop, d (m + p) = d m := by
  sorry

end Erdos341
