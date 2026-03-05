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
# Erdős Problem 339

*Reference:* [erdosproblems.com/339](https://www.erdosproblems.com/339)

Let $A \subseteq \mathbb{N}$ be a basis of order $r$. Must the set of integers representable as
the sum of exactly $r$ distinct elements from $A$ have positive lower density?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[HHP03] Hegyvári, N., Hennecart, F. and Plagne, A., *A proof of two Erdős' conjectures on
restricted addition and further results*. J. Reine Angew. Math. (2003).
-/

open Set Filter BigOperators Classical

namespace Erdos339

/-- The set of all sums of exactly $k$ elements from $A$ (with repetition allowed). -/
def exactSumset (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- $A \subseteq \mathbb{N}$ is an additive basis of order $r$ if every sufficiently large natural
number is the sum of at most $r$ elements from $A$ (with repetition). -/
def IsAdditiveBasis (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ r, n ∈ exactSumset A k

/-- The set of integers representable as the sum of exactly $r$ distinct elements from $A$. -/
def distinctExactSumset (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (s : Finset ℕ), ↑s ⊆ A ∧ s.card = r ∧ s.sum id = n}

/-- The lower density of $A \subseteq \mathbb{N}$:
$$d_*(A) = \liminf_{N\to\infty} \frac{|A \cap \{0, 1, \ldots, N-1\}|}{N}$$ -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem 339 [ErGr80, p.52]:

Let $A \subseteq \mathbb{N}$ be a basis of order $r$. Must the set of integers representable as
the sum of exactly $r$ distinct elements from $A$ have positive lower density?

The answer is yes, as proved by Hegyvári, Hennecart, and Plagne [HHP03].
-/
@[category research solved, AMS 11]
theorem erdos_339 :
    answer(True) ↔ ∀ (A : Set ℕ) (r : ℕ),
      IsAdditiveBasis A r →
      0 < lowerDensity (distinctExactSumset A r) := by
  sorry

end Erdos339
