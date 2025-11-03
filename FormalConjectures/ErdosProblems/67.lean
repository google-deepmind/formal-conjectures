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
# Erdős Problem 67

*References:*
- [erdosproblems.com/67](https://www.erdosproblems.com/66)
- [Ta16] Tao, Terence, The Erdős discrepancy problem. Discrete Anal. (2016), Paper No. 1, 29.
-/
open Filter

namespace Erdos67

/--
**The Erdős discrepancy problem**

If $f\colon \mathbb N \rightarrow \{-1, +1\}$ then is it true that for every $C>0$ there
exist $d, m \ge 1$ such that $$\left\lvert \sum_{1\leq k\leq m}f(kd)\right\rvert > C?$$
This is true, and was proved by Tao [Ta16]
-/
@[category research solved, AMS 11]
theorem erdos_67 (f : ℕ → ({-1, 1} : Finset ℝ)) (C : ℝ) (hC : 0 < C) : ∃ᵉ (d ≥ 1) (m ≥ 1),
    C < |(∑ k ∈ Finset.Icc 1 m, (f (k * d)).1)| := by
  sorry

/--
**The Erdős discrepancy problem (complex variant)**

If $f\colon \mathbb N \rightarrow S^1 ⊆ ℂ$ then is it true that for every $C>0$ there
exist $d, m \ge 1$ such that $$\left\lvert \sum_{1\leq k\leq m}f(kd)\right\rvert > C?$$
This is true, and was proved by Tao [Ta16]
-/
@[category research solved, AMS 11]
theorem erdos_67.variants.complex (f : ℕ → ({c | ‖c‖ = 1} : Set ℂ)) (C : ℝ) (hC : 0 < C) :
    ∃ᵉ (d ≥ 1) (m ≥ 1), C < ‖(∑ k ∈ Finset.Icc 1 m, (f (k * d)).1)‖  := by
  sorry


end Erdos67
