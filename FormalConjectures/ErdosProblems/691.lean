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
# Erdős Problem 691

*Reference:* [erdosproblems.com/691](https://www.erdosproblems.com/691)

Given $A \subseteq \mathbb{N}$, let $M_A = \{n \geq 1 : a \mid n \text{ for some } a \in A\}$
be the set of multiples of $A$. A sequence $A$ for which $M_A$ has density $1$ is called
a *Behrend sequence*.

For pairwise coprime sets of integers (all $\geq 2$), a necessary and sufficient condition
for $A$ to be a Behrend sequence is $\sum_{a \in A} 1/a = \infty$.

The general characterization remains open.

[Er79e] Erdős, P., _Some old and new problems on combinatorial number theory_ (1979), p.77.
-/

open Classical Filter

open scoped BigOperators Topology

namespace Erdos691

/-- Count of integers $m \in \{1, \ldots, N\}$ such that some element of $A$ divides $m$. -/
noncomputable def countMultiples (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ∃ a ∈ A, a ∣ (n + 1))).card

/-- A set $A \subseteq \mathbb{N}$ is a *Behrend sequence* if the set of multiples of $A$ has
natural density $1$, i.e., $|M_A \cap \{1, \ldots, N\}| / N \to 1$ as $N \to \infty$. -/
def IsBehrend (A : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => (countMultiples A (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
    atTop (nhds 1)

/-- A set of natural numbers is *pairwise coprime*. -/
def SetPairwiseCoprime (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b

/-- The sum of reciprocals of elements of $A$ diverges: for every bound $C > 0$,
some finite subset of $A$ achieves a reciprocal sum exceeding $C$. -/
def ReciprocalSumDiverges (A : Set ℕ) : Prop :=
  ∀ C : ℝ, C > 0 → ∃ F : Finset ℕ, (∀ a ∈ F, a ∈ A) ∧
    C < ∑ a ∈ F, (1 : ℝ) / (a : ℝ)

/--
Erdős Problem 691 (pairwise coprime case) [Er79e]:
If $A$ is a set of pairwise coprime integers (all $\geq 2$), then $A$ is a Behrend
sequence if and only if the sum of reciprocals $\sum_{a \in A} 1/a$ diverges.
-/
@[category research solved, AMS 11]
theorem erdos_691 (A : Set ℕ) (hA : ∀ a ∈ A, a ≥ 2)
    (hCoprime : SetPairwiseCoprime A) :
    IsBehrend A ↔ ReciprocalSumDiverges A := by
  sorry

end Erdos691
