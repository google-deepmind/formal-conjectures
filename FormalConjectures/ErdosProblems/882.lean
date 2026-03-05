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
# Erdős Problem 882

*Reference:* [erdosproblems.com/882](https://www.erdosproblems.com/882)

What is the size of the largest $A \subseteq \{1, \ldots, n\}$ such that the set of all
non-empty subset sums $\{ \sum_{a \in S} a : \emptyset \neq S \subseteq A \}$ is primitive
(no two distinct elements divide each other)?

A problem of Erdős and Sárkőzy [Er98]. The greedy algorithm shows
$|A| \geq (1 - o(1)) \log_3 n$. Erdős, Lev, Rauzy, Sándor, and Sárközy [ELRSS99]
proved $|A| > \log_2 n - 1$ is achievable. The upper bound
$|A| \leq \log_2 n + \tfrac{1}{2} \log_2 \log n + O(1)$ follows from the distinct subset
sums property. It is conjectured that $|A| \leq \log_2 n + O(1)$.

[Er98] Erdős, P., _Some of my favourite problems which recently have been solved_,
Challenges for the 21st century (Singapore, 2000), 2001.

[ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C., and Sárközy, A., _Greedy algorithm,
arithmetic progressions, subset sums and divisibility_, 1999.
-/

open Finset BigOperators Real

namespace Erdos882

/-- The set of all non-empty subset sums of a finset $A$ of natural numbers. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (· ≠ ∅)).image (fun S => S.sum id)

/-- A finset of natural numbers is *primitive* if no element divides another
distinct element. -/
def IsPrimitive (B : Finset ℕ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ∣ b → a = b

/-- The maximum size of $A \subseteq \{1, \ldots, n\}$ whose non-empty subset sums form a
primitive set. -/
noncomputable def maxPrimitiveSubsetSumSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = k ∧
    IsPrimitive (subsetSums A)}

/--
Erdős Problem 882, conjectured upper bound [Er98]:

There exists a constant $C$ such that for all sufficiently large $n$,
the maximum size of $A \subseteq \{1, \ldots, n\}$ whose non-empty subset sums are
primitive satisfies $|A| \leq \log_2 n + C$.
-/
@[category research open, AMS 5 11]
theorem erdos_882 :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (maxPrimitiveSubsetSumSize n : ℝ) ≤ Real.log n / Real.log 2 + C := by
  sorry

/--
Erdős Problem 882, lower bound [ELRSS99]:

For all sufficiently large $n$, there exists $A \subseteq \{1, \ldots, n\}$ with
$|A| > \log_2 n - 1$ such that the non-empty subset sums of $A$ form a primitive set.
-/
@[category research solved, AMS 5 11]
theorem erdos_882.variants.lower_bound :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (maxPrimitiveSubsetSumSize n : ℝ) > Real.log n / Real.log 2 - 1 := by
  sorry

end Erdos882
