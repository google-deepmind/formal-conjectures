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
import Mathlib.Data.Nat.Lcm
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Problem 856

*Reference:* [erdosproblems.com/856](https://www.erdosproblems.com/856)

Let $k\ge 3$ and $f_k(N)$ be the maximum value of $\sum_{n\in A}\frac{1}{n}$,
where $A$ ranges over all subsets of $\{1,\ldots,N\}$ which contain no subset
of size $k$ with the same pairwise least common multiple.

Estimate $f_k(N)$.
-/

namespace Erdos856

open Filter Asymptotics Real

/--
A subset `A` of `{1,…,N}` is *admissible* if it contains no `k`-element subset
whose elements have a common pairwise least common multiple.
-/
private def admissible (A : Finset ℕ) (k : ℕ) : Prop :=
  ¬ ∃ B ⊆ A, B.card = k ∧ ∃ L : ℕ, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → Nat.lcm x y = L

/--
The sum of reciprocals of elements of a finite set.
-/
private def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n in A, (1 / n : ℝ)

/--
The maximum value of the reciprocal sum over admissible subsets of `{1,…,N}`.
-/
noncomputable def f (k : ℕ) (N : ℕ) : ℝ :=
  sSup { reciprocalSum A | A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ admissible A k }

/--
Conjecture: For every fixed $k\ge3$, $f_k(N) = o(\log N)$.
-/
@[category research open, AMS 52]
theorem erdos_856 : ∀ k ≥ 3, (fun N : ℕ => f k N) =o[atTop] (fun N => Real.log (N : ℝ)) := by
  sorry

-- TODO(firsching): formalize other results from the additional material

end Erdos856
