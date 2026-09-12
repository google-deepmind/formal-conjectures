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
# Erdős Problem 980

*Reference:* [erdosproblems.com/980](https://www.erdosproblems.com/980)
-/

open Filter Nat Asymptotics
open scoped Topology

namespace Erdos980

/-- `n` is a $k$th-power residue modulo `p`. -/
def IsKthPowerResidue (k p n : ℕ) : Prop :=
  ∃ a : ℕ, a ^ k ≡ n [MOD p]

/-- The least $k$th-power nonresidue of a prime $p$: the least positive integer that is not a
$k$th-power residue modulo $p`. -/
noncomputable def leastKthPowerNonresidue (k p : ℕ) : ℕ :=
  sInf { n : ℕ | 0 < n ∧ ¬ IsKthPowerResidue k p n }

/--
Let $k\geq 2$ and $n_k(p)$ denote the least $k$th power nonresidue of $p$. Is it true that
$$
\sum_{p<x} n_k(p)\sim c_k \frac{x}{\log x}
$$
for some constant $c_k>0$?
-/
@[category research open, AMS 11]
theorem erdos_980 :
    answer(sorry) ↔
      ∀ k ≥ 2, ∃ c : ℝ, 0 < c ∧
        IsEquivalent atTop
          (fun x : ℕ ↦ ∑ p ∈ (Finset.range x).filter Nat.Prime,
            (leastKthPowerNonresidue k p : ℝ))
          (fun x : ℕ ↦ c * x / Real.log x) := by
  sorry

end Erdos980
