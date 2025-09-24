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
import Mathlib/Data/PNat/Basic
import Mathlib/Analysis/SpecialFunctions/Exp

/-!
# Erdős Problem 312 — Conjecture Statement

We state the conjecture only (no proof).
-/

noncomputable section
open scoped BigOperators

namespace FormalConjectures
namespace ErdosProblems
namespace «312»

/-- Harmonic sum of a finite family of positive integers. -/
def hsum {n : ℕ} (a : Fin n → ℕ+) : ℝ :=
  ∑ i, ((a i : ℕ) : ℝ)⁻¹

/--
Core predicate with parameter `c > 0`:

For all `K > 1` and finite families `a`, if `hsum a > K` then there exists
`S ⊆ {0,…,n-1}` with `1 - exp (-(c*K)) < ∑_{i∈S} 1/(a i) ≤ 1`.
-/
def ConjectureWith (c : ℝ) : Prop :=
  0 < c ∧
  ∀ ⦃K : ℝ⦄, 1 < K →
  ∀ ⦃n : ℕ⦄, ∀ (a : Fin n → ℕ+),
    hsum a > K →
    ∃ S : Finset (Fin n),
      1 - Real.exp (-(c*K)) < ∑ i in S, ((a i : ℕ) : ℝ)⁻¹ ∧
      (∑ i in S, ((a i : ℕ) : ℝ)⁻¹) ≤ 1

/-- There exists some `c > 0` for which `ConjectureWith c` holds. -/
@[AMS "Erdős 312"]
@[ProblemCategory "Additive/Combinatorial Number Theory"]
def Conjecture : Prop := ∃ c : ℝ, ConjectureWith c

end «312»
end ErdosProblems
end FormalConjectures
