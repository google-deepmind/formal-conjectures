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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 343

*References:*
- [erdosproblems.com/343](https://www.erdosproblems.com/343)
-/

@[expose] public section

open Filter Topology MeasureTheory SimpleGraph

namespace Erdos343

/-- Number of elements of a multiset, counted with multiplicity, in $[1,N]$. -/
def intervalCount (A : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 1 N, A n

/-- Finite subsums of a multiset represented by its multiplicity function. -/
def subsetSums (A : ℕ → ℕ) : Set ℕ :=
  {s | ∃ B : ℕ →₀ ℕ, (∀ n, B n ≤ A n) ∧ s = ∑ n ∈ B.support, B n * n}

/-- A multiset with at least linear growth of its counting function has an infinite
arithmetic progression among its finite subsums. Proved by Szemerédi and Vu [SzVu06]. -/
@[category research solved, question, AMS 11]
theorem erdos_343 (A : ℕ → ℕ)
    (hA : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → c * N ≤ intervalCount A N) :
    ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ subsetSums A := by
  sorry

end Erdos343
