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
# Erdős Problem 338

*Reference:* [erdosproblems.com/338](https://www.erdosproblems.com/338)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open scoped BigOperators

namespace Erdos338

/-- The set of all sums of exactly $k$ elements from $A$ (with repetition allowed). -/
def exactSumset (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- $A \subseteq \mathbb{N}$ is an additive basis of order $h$ if every sufficiently large
natural number is the sum of at most $h$ elements from $A$ (with repetition). -/
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ h, n ∈ exactSumset A k

/-- $n$ is the sum of at most $t$ distinct elements from $A$:
there exists a finite subset $s \subseteq A$ with $|s| \leq t$ and $\sum_{x \in s} x = n$. -/
def IsDistinctSum (A : Set ℕ) (t : ℕ) (n : ℕ) : Prop :=
  ∃ (s : Finset ℕ), ↑s ⊆ A ∧ s.card ≤ t ∧ s.sum id = n

/-- $A$ has restricted order at most $t$ if every sufficiently large natural number
is the sum of at most $t$ distinct elements from $A$. -/
def HasRestrictedOrderAtMost (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, IsDistinctSum A t n

/-- $A$ has a restricted order (i.e., some finite restricted order exists). -/
def HasRestrictedOrder (A : Set ℕ) : Prop :=
  ∃ t : ℕ, HasRestrictedOrderAtMost A t

/--
Erdős Problem 338 [ErGr80]:

The restricted order of a basis $A \subseteq \mathbb{N}$ is the least integer $t$ (if it exists)
such that every sufficiently large integer is the sum of at most $t$ distinct elements from $A$.

Bateman observed that for $h \geq 3$, the basis $A = \{1\} \cup \{x > 0 : h \mid x\}$ has order
$h$ but no restricted order. Kelly showed that any basis of order $2$ has restricted order at most
$4$. Hennecart constructed a basis of order $2$ with restricted order exactly $4$.

The problem asks: what are necessary and sufficient conditions for the restricted order to exist,
and can it be bounded in terms of the order of the basis?

A specific sub-conjecture asks: if $A \setminus F$ is a basis of the same order $h$ for every
finite set $F \subseteq \mathbb{N}$, must $A$ have a restricted order?
-/
@[category research open, AMS 5 11]
theorem erdos_338 :
    ∀ (A : Set ℕ) (h : ℕ),
      (∀ (F : Finset ℕ), IsAdditiveBasis (A \ ↑F) h) →
      HasRestrictedOrder A := by
  sorry

end Erdos338
