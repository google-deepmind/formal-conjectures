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

import FormalConjecturesUtil

/-!
# Erdős Problem 361

*Reference:* [erdosproblems.com/361](https://www.erdosproblems.com/361)
-/

open Filter

namespace Erdos361

/--
`AvoidsSubsetSum n A` means that no subset $B \subseteq A$ has sum equal to $n$.
-/
def AvoidsSubsetSum (n : ℕ) (A : Finset ℕ) : Prop :=
  ∀ B ∈ A.powerset, n ≠ ∑ a ∈ B, a

instance (n : ℕ) (A : Finset ℕ) : Decidable (AvoidsSubsetSum n A) := by
  unfold AvoidsSubsetSum
  infer_instance

/--
The largest cardinality of a set $A \subseteq \{1, \ldots, N\}$ such that no subset of $A$
sums to $n$.
-/
def maxSubsetSumAvoidingCard (N n : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (AvoidsSubsetSum n)).sup Finset.card

/--
For fixed $c$ and $n$, this is the size of the largest set
$A \subseteq \{1, \ldots, \lfloor cn \rfloor\}$ such that no subset of $A$ sums to $n$.
-/
noncomputable def subsetSumAvoidanceNumber (c : ℝ) (n : ℕ) : ℕ :=
  maxSubsetSumAvoidingCard ⌊c * n⌋₊ n

/--
For target $4$ and universe $\{1, 2, 3\}$, the maximum is $2$: the full set is invalid because
its subset $\{1, 3\}$ sums to $4$.
-/
@[category test, AMS 11]
theorem maxSubsetSumAvoidingCard_three_four : maxSubsetSumAvoidingCard 3 4 = 2 := by
  native_decide

/--
Let $c > 0$ and $n$ be some large integer. What is the size of the largest set
$A \subseteq \{1, \ldots, \lfloor c n \rfloor\}$ such that $n$ is not a sum of a subset of $A$?
Does this depend on $n$ in an irregular way?
-/
@[category research open, AMS 11]
theorem erdos_361 (c : ℝ) (hc : 0 < c) :
    subsetSumAvoidanceNumber c = answer(sorry) := by
  sorry

/--
Asymptotic version of Erdős Problem 361: determine the order of growth of the largest cardinality
as $n \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_361.asymptotic (c : ℝ) (hc : 0 < c) :
    (fun n ↦ (subsetSumAvoidanceNumber c n : ℝ)) =Θ[atTop]
      (answer(sorry) : ℕ → ℝ) := by
  sorry

end Erdos361
