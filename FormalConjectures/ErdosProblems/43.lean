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
# Erdős Problem 43

*Reference:* [erdosproblems.com/43](https://www.erdosproblems.com/43)

If $A, B \subseteq \{1, \ldots, N\}$ are Sidon sets with $(A-A) \cap (B-B) = \{0\}$, is it true
that $\binom{|A|}{2} + \binom{|B|}{2} \leq \binom{f(N)}{2} + O(1)$, where $f(N)$ is the maximum
size of a Sidon set in $\{1, \ldots, N\}$?

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics, Paul Erdős is Eighty **2** (1996), 1–25.

OEIS: A143824, A227590, A003022
-/

open Finset Filter

namespace Erdos43

/-- Two sets $A$, $B$ have disjoint difference sets (intersecting only at $0$):
    $(A - A) \cap (B - B) = \{0\}$. Equivalently, if $a_1 - a_2 = b_1 - b_2$ for
    $a_1, a_2 \in A$ and $b_1, b_2 \in B$, then $a_1 = a_2$ and $b_1 = b_2$. -/
def DisjointDifferences (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B,
    (a₁ : ℤ) - (a₂ : ℤ) = (b₁ : ℤ) - (b₂ : ℤ) → a₁ = a₂ ∧ b₁ = b₂

/-- If $A, B \subseteq \{1, \ldots, N\}$ are two Sidon sets such that
    $(A - A) \cap (B - B) = \{0\}$, is it true that
    $$\binom{|A|}{2} + \binom{|B|}{2} \leq \binom{f(N)}{2} + O(1),$$
    where $f(N)$ is the maximum possible size of a Sidon set in $\{1, \ldots, N\}$?

    Here $S$ represents a maximum-size Sidon set in $\{1, \ldots, N\}$, so $|S| = f(N)$.
    The $O(1)$ term is captured by the absolute constant $C$.

    *Reference:* [Er95]
-/
@[category research open, AMS 5 11]
theorem erdos_43 : answer(sorry) ↔ ∃ C : ℕ, ∀ (N : ℕ) (A B S : Finset ℕ),
    IsSidon (A : Set ℕ) → IsSidon (B : Set ℕ) → IsSidon (S : Set ℕ) →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
    (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) →
    (∀ T : Finset ℕ, IsSidon (T : Set ℕ) → (∀ t ∈ T, 1 ≤ t ∧ t ≤ N) → T.card ≤ S.card) →
    DisjointDifferences A B →
    Nat.choose A.card 2 + Nat.choose B.card 2 ≤ Nat.choose S.card 2 + C := by
  sorry

/-- Secondary question from Erdős Problem 43: if $|A| = |B|$, can the bound be improved to
    $\binom{|A|}{2} + \binom{|B|}{2} \leq (1 - c + o(1)) \binom{f(N)}{2}$ for some constant
    $c > 0$?

    Barreto showed the answer is no: for infinitely many $N$, there exist equal-sized Sidon sets
    $A, B$ with disjoint differences achieving $(1 - o(1)) \binom{f(N)}{2}$.

    This is formalized as: for every $c > 0$, for all sufficiently large $N$, there exist
    equal-sized Sidon sets $A, B \subseteq \{1, \ldots, N\}$ with disjoint differences such that
    $\binom{|A|}{2} + \binom{|B|}{2} > (1 - c) \binom{f(N)}{2}$.

    *Reference:* [Er95]
-/
@[category research solved, AMS 5 11]
theorem erdos_43_equal_size_negative :
    ∀ (c : ℝ) (_ : 0 < c), ∀ᶠ N in Filter.atTop,
    ∃ (A B S : Finset ℕ),
    IsSidon (A : Set ℕ) ∧ IsSidon (B : Set ℕ) ∧ IsSidon (S : Set ℕ) ∧
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) ∧
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) ∧
    (∀ T : Finset ℕ, IsSidon (T : Set ℕ) → (∀ t ∈ T, 1 ≤ t ∧ t ≤ N) → T.card ≤ S.card) ∧
    A.card = B.card ∧
    DisjointDifferences A B ∧
    (1 - c) * Nat.choose S.card 2 < ↑(Nat.choose A.card 2 + Nat.choose B.card 2) := by
  sorry

end Erdos43
