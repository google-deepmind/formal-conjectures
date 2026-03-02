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
# Erdős Problem 1139

*Reference:* [erdosproblems.com/1139](https://www.erdosproblems.com/1139)
-/

open Nat Filter
open scoped ArithmeticFunction.Omega
open scoped Topology

namespace Erdos1139

/--
Let $1\leq u_1 < u_2 < \cdots$ be the sequence of integers with at most $2$ prime factors.
Is it true that $$\limsup_{k \to \infty} \frac{u_{k+1}-u_k}{\log k}=\infty?$$
-/
@[category research open, AMS 11]
theorem erdos_1139 :
    answer(sorry) ↔
      letI u := Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)
      atTop.limsup (fun k : ℕ ↦ (((u (k + 1) : ℝ) - (u k : ℝ)) / Real.log (↑k + 1) : EReal)) = ⊤ := by
  sorry

end Erdos1139
