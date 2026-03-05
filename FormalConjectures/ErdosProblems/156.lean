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
# Erdős Problem 156

*Reference:* [erdosproblems.com/156](https://www.erdosproblems.com/156)

A question of Erdős, Sárközy, and Sós [ESS94]. Ruzsa [Ru98b] constructed a maximal Sidon set
of size $\ll (N \log N)^{1/3}$, but whether $O(N^{1/3})$ is achievable remains open.

[ESS94] Erdős, P., Sárközy, A., and Sós, V. T.

[Ru98b] Ruzsa, I. Z.
-/

open Filter

open scoped Topology Real

namespace Erdos156

/-- A finite set of natural numbers is a Sidon set (also called a $B_2$ set) if all
pairwise sums $a + b$ (allowing $a = b$) are distinct: whenever $a + b = c + d$
with $a, b, c, d \in A$, we have $\{a, b\} = \{c, d\}$ as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon set $A \subseteq \{0, \ldots, N-1\}$ is maximal (in $\{0, \ldots, N-1\}$) if no
element of $\{0, \ldots, N-1\} \setminus A$ can be added to $A$ while preserving the Sidon
property. -/
def IsMaximalSidonSet (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range N ∧
  IsSidonSet A ∧
  ∀ n ∈ Finset.range N, n ∉ A → ¬IsSidonSet (insert n A)

/--
Erdős–Sárközy–Sós Conjecture (Problem 156) [ESS94]:

Does there exist a maximal Sidon set $A \subset \{1, \ldots, N\}$ of size $O(N^{1/3})$?

The greedy algorithm produces a maximal Sidon set of size $\gg N^{1/3}$ (this is known).
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N \log N)^{1/3}$, which is
close but does not reach $O(N^{1/3})$.

Formalized as: there exists a constant $C > 0$ such that for all sufficiently large $N$,
there exists a maximal Sidon set $A \subseteq \{0, \ldots, N-1\}$ with
$|A| \leq C \cdot N^{1/3}$.
-/
@[category research open, AMS 5 11]
theorem erdos_156 : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧
          (A.card : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  sorry

end Erdos156
