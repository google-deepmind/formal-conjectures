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
# Erdős Problem 245

*Reference:* [erdosproblems.com/245](https://www.erdosproblems.com/245)
-/

namespace Erdos245

open Filter Erdos245

open scoped Pointwise Topology

/--
Let $A\subseteq\mathbb{N}$ be an infinite set such that $|A\cap \{1, ..., N\}| = o(N)$.
Is it true that
$$
\limsup_{N\to\infty}\frac{|(A + A)\cap \{1, ..., N\}|}{|A \cap \{1, ..., N\}|} \geq 3?
$$

The answer is yes, proved by Freiman [Fr73].

[Fr73] Fre\u{\i}man, G. A., _Foundations of a structural theory of set addition_. (1973), vii+108.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/245", AMS 5 11]
theorem erdos_245 :
    answer(True) ↔ ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto (fun N ↦ (A.interIcc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (𝓝 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A).interIcc 1 ⌊N⌋₊ |>.ncard : EReal) / (A.interIcc 1 ⌊N⌋₊).ncard := by
  sorry

/--
Let $A\subseteq\mathbb{N}$ be an infinite set such that $|A\cap \{1, ..., N\}| = o(N)$.
Then
$$
\limsup_{N\to\infty}\frac{|(A + A)\cap \{1, ..., N\}|}{|A \cap \{1, ..., N\}|} \geq 2.
$$
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/245", AMS 5 11]
theorem erdos_245.variants.two (A : Set ℕ) (h_inf : A.Infinite)
    (hf : atTop.Tendsto (fun N ↦ (A.interIcc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (𝓝 0)) :
    2 ≤ atTop.limsup
      fun N : ℝ ↦ ((A + A).interIcc 1 ⌊N⌋₊ |>.ncard : EReal) / (A.interIcc 1 ⌊N⌋₊).ncard := by
  sorry

end Erdos245
