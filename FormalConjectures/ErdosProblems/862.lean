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
# Erdős Problem 862

*Reference:* [erdosproblems.com/862](https://www.erdosproblems.com/862)

Let $A_1(N)$ be the number of maximal Sidon subsets of $\{1,\ldots,N\}$. Is it true that
$A_1(N) < 2^{o(N^{1/2})}$? Is it true that $A_1(N) > 2^{N^c}$ for some constant $c > 0$?

A problem of Cameron and Erdős [Er92c, p.39].

**Status**: Both questions are resolved by results of Saxton and Thomason [SaTh15].
They prove that the number of Sidon sets in $\{1,\ldots,N\}$ is at least
$2^{(1.16+o(1))N^{1/2}}$. Since each Sidon set is contained in a maximal Sidon set, and each
maximal Sidon set contains at most $2^{(1+o(1))N^{1/2}}$ Sidon subsets, it follows that
$A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}$. This shows the first conjecture is false and the second
is true.

[Er92c] Erdős, P., *Some of my favourite problems in various branches of combinatorics*,
Matematiche (Catania) 47 (1992), no. 2, 231–240.

[SaTh15] Saxton, D. and Thomason, A., *The number of Sidon sets and the maximum size
of Sidon sets contained in a sparse random set of integers*, Random Structures & Algorithms
46 (2015), no. 1, 1–25.
-/

open Finset Classical

namespace Erdos862

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon subset of $\{1,\ldots,N\}$ is maximal if no element of $\{1,\ldots,N\}$ can be added
while keeping it Sidon. -/
def IsMaximalSidonIn (S : Finset ℕ) (N : ℕ) : Prop :=
  S ⊆ Icc 1 N ∧ IsSidonSet S ∧
    ∀ x ∈ Icc 1 N, x ∉ S → ¬IsSidonSet (S ∪ {x})

/-- $A_1(N)$ is the number of maximal Sidon subsets of $\{1,\ldots,N\}$. -/
noncomputable def countMaximalSidon (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun S => IsMaximalSidonIn S N)).card

/--
Erdős Problem 862, first question (Cameron–Erdős [Er92c], disproved by Saxton–Thomason [SaTh15]):

$A_1(N) \not< 2^{o(N^{1/2})}$. More precisely, for all sufficiently large $N$,
$A_1(N) \geq 2^{0.16 \cdot N^{1/2}}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_862 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countMaximalSidon N : ℝ) ≥ (2 : ℝ) ^ ((0.16 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
  sorry

/--
Erdős Problem 862, second question (Cameron–Erdős [Er92c], proved by Saxton–Thomason [SaTh15]):

$A_1(N) > 2^{N^c}$ for some $c > 0$, for all sufficiently large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_862.variants.second_question :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countMaximalSidon N : ℝ) > (2 : ℝ) ^ ((N : ℝ) ^ c) := by
  sorry

end Erdos862
