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
# Erdős Problem 845

*Reference:* [erdosproblems.com/845](https://www.erdosproblems.com/845)
-/

/--
Let $C > 0$. Is it true that the set of integers of the form $n = b_1 + \cdots + b_t$,
with $b_1 < \cdots < b_t$, where $b_i = 2^{k_i}3^{l_i}$ for $1 \leq i\leq t$ and
$b_t \leq Cb_1$ has density $0$?
-/
@[category research open, AMS 11]
theorem erdos_845 (C : ℝ) (hC : 0 < C) :
    let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
    { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
      (hB : B.sup f ≤ C * B.inf' h f) }.HasDensity 0 ↔ answer(sorry) := by
  sorry
