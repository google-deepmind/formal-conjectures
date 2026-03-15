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
# Erdős Problem 732

*Reference:* [erdosproblems.com/732](https://www.erdosproblems.com/732)

Call a sequence $1 < X_1 \leq \cdots \leq X_m \leq n$ block-compatible if there is a pairwise
balanced block design $A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ such that $|A_i| = X_i$ for
$1 \leq i \leq m$. (A pairwise block design means every pair in $\{1, \ldots, n\}$ is contained in
exactly one $A_i$.)

Is there some constant $c > 0$ such that for all large $n$ there are
$\geq \exp(c \cdot \sqrt{n} \cdot \log n)$ many block-compatible sequences for $\{1, \ldots, n\}$?

Proved by Alon, who showed there are at least $2^{(1/2 + o(1)) \cdot \sqrt{n} \cdot \log n}$
block-compatible sequences. Erdős proved the upper bound $\exp(O(\sqrt{n} \cdot \log n))$.

[Er81] Erdős, P., _Problems and results in graph theory and combinatorics_,
Proceedings of the Southeastern Conference on Combinatorics, Graph Theory,
and Computing (1981), p. 35.
-/

namespace Erdos732

/-- A pairwise balanced design (PBD) on `Fin n`: a finset of blocks where each block
has at least 2 elements and every pair of distinct elements belongs to exactly
one block. -/
def IsPBD (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, 2 ≤ B.card) ∧
  (∀ i j : Fin n, i ≠ j → ∃! B, B ∈ blocks ∧ i ∈ B ∧ j ∈ B)

/-- The multiset of block sizes of a family of sets. -/
def blockSizeMultiset (n : ℕ) (blocks : Finset (Finset (Fin n))) : Multiset ℕ :=
  blocks.val.map Finset.card

/-- A multiset of natural numbers is block-compatible for $n$ if there exists a PBD
on `Fin n` with those block sizes. -/
def IsBlockCompatible (n : ℕ) (M : Multiset ℕ) : Prop :=
  ∃ blocks : Finset (Finset (Fin n)), IsPBD n blocks ∧ blockSizeMultiset n blocks = M

/--
Erdős Problem 732 [Er81]:

There exists a constant $c > 0$ such that for all sufficiently large $n$, the number
of block-compatible sequences (multisets of block sizes from PBDs on $\{1, \ldots, n\}$)
is at least $\exp(c \cdot \sqrt{n} \cdot \log n)$.
-/
@[category research solved, AMS 5]
theorem erdos_732 : answer(True) ↔ ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ S : Finset (Multiset ℕ),
      (∀ M ∈ S, IsBlockCompatible n M) ∧
      (S.card : ℝ) ≥ Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by
  sorry

end Erdos732
