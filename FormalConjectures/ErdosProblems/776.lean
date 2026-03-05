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
# Erdős Problem 776

*Reference:* [erdosproblems.com/776](https://www.erdosproblems.com/776)

A problem of Erdős and Trotter. Let $r \geq 2$ and $A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$
be an antichain such that every set size that appears does so at least $r$ times. How large must
$n$ be (as a function of $r$) to ensure such a family achieves $n - 3$ distinct set sizes?

For $r = 1$ and $n > 3$ the maximum possible number of distinct sizes is $n - 2$. For $r > 1$ and
$n$ sufficiently large, $n - 3$ is achievable but $n - 2$ is never achievable.
-/

namespace Erdos776

/-- A family of sets is an antichain if no set is a subset of another. -/
def IsAntichain (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬(A ⊆ B)

/-- Every size that appears in the family appears at least $r$ times. -/
def HasMinMultiplicity (F : Finset (Finset ℕ)) (r : ℕ) : Prop :=
  ∀ t : ℕ, (∃ A ∈ F, A.card = t) →
    r ≤ (F.filter (fun A => A.card = t)).card

/-- The number of distinct sizes of sets in the family. -/
def numDistinctSizes (F : Finset (Finset ℕ)) : ℕ :=
  (F.image Finset.card).card

/-- All sets in the family are subsets of $\{0, \ldots, n-1\}$. -/
def AllSubsetsOfRange (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ A ∈ F, ∀ x ∈ A, x < n

/--
Erdős Problem 776:
For every $r \geq 2$, there exists $N_0$ such that for all $n \geq N_0$ there is an antichain
$F$ of subsets of $\{0, \ldots, n-1\}$ in which every size class has at least $r$ members
and the family achieves exactly $n - 3$ distinct sizes of sets.

The problem asks for the growth rate of $N_0$ as a function of $r$.
-/
@[category research open, AMS 5]
theorem erdos_776 :
    ∀ r : ℕ, r ≥ 2 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ F : Finset (Finset ℕ),
          AllSubsetsOfRange F n ∧
          IsAntichain F ∧
          HasMinMultiplicity F r ∧
          numDistinctSizes F = n - 3 := by
  sorry

/--
For $r = 1$ and $n > 3$, an antichain of subsets of $\{0, \ldots, n-1\}$ can achieve
at most $n - 2$ distinct sizes, and this is tight.
-/
@[category research solved, AMS 5]
theorem erdos_776.variants.r_eq_1 :
    ∀ n : ℕ, n > 3 →
      (∃ F : Finset (Finset ℕ),
        AllSubsetsOfRange F n ∧
        IsAntichain F ∧
        numDistinctSizes F = n - 2) ∧
      (∀ F : Finset (Finset ℕ),
        AllSubsetsOfRange F n →
        IsAntichain F →
        numDistinctSizes F ≤ n - 2) := by
  sorry

/--
For $r \geq 2$, no antichain with minimum multiplicity $r$ can achieve $n - 2$
distinct sizes (for any $n$).
-/
@[category research solved, AMS 5]
theorem erdos_776.variants.upper_bound :
    ∀ r : ℕ, r ≥ 2 → ∀ n : ℕ,
      ∀ F : Finset (Finset ℕ),
        AllSubsetsOfRange F n →
        IsAntichain F →
        HasMinMultiplicity F r →
        numDistinctSizes F ≤ n - 3 := by
  sorry

end Erdos776
