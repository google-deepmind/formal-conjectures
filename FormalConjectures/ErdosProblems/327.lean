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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 327

*References:*
- [erdosproblems.com/327](https://www.erdosproblems.com/327)
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathématique (1980).
-/

@[expose] public section

namespace Erdos327

/-- **Question 1** (open, as stated on the problem page), in the strong reading of
"substantially more than the odd numbers": there is a uniform `ε > 0` such that for
*every sufficiently large* `N` some admissible `A ⊆ {1,…,N}` has `|A| ≥ (1/2 + ε) N`. -/
def Question1 : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ Admissible1 A ∧ (1 / 2 + ε) * (N : ℝ) ≤ (A.card : ℝ)

/-- **Question 1**, weak reading: the same, but only for *infinitely many* `N`
(i.e. `limsup f₁(N)/N > 1/2`). -/
def Question1Weak : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ Admissible1 A ∧ (1 / 2 + ε) * (N : ℝ) ≤ (A.card : ℝ)

/-- **Question 2** (open on the problem page): must every `A ⊆ {1,…,N}` with the second
condition have `|A| = o(N)`, uniformly in `A`?  I.e. for every `ε > 0`, for all large `N`,
every such `A` has `|A| ≤ ε N`. -/
def Question2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N → Admissible2 A → (A.card : ℝ) ≤ ε * (N : ℝ)

/-- Positive-density sets satisfying the second condition exist for every sufficiently large bound. -/
def PositiveDensity2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ Admissible2 A ∧ c * (N : ℝ) ≤ (A.card : ℝ)

/--
Suppose $A\subseteq \{1,\ldots,N\}$ is such that if $a,b\in A$ and $a\neq b$ then
$a+b\nmid ab$. Can $A$ be 'substantially more' than the odd numbers?

Here this means that a fixed positive density improvement over $1/2$ is possible
for arbitrarily large $N$.
-/
@[category research open, AMS 11]
theorem erdos_327.parts.i : answer(sorry) ↔ Question1Weak := by
  sorry

/--
What if $a,b\in A$ with $a\neq b$ implies $a+b\nmid 2ab$? Must $\lvert A\rvert=o(N)$?
-/
@[category research open, AMS 11]
theorem erdos_327.parts.ii : answer(sorry) ↔ Question2 := by
  sorry

/-- Does the first condition allow a fixed positive density improvement over $1/2$
for every sufficiently large $N$? -/
@[category research open, AMS 11]
theorem erdos_327.variants.eventual_density : answer(sorry) ↔ Question1 := by
  sorry

/-! ## Logical relations between the density formulations -/

/-- The strong reading of Question 1 implies the weak reading. -/
@[category test, AMS 11]
theorem question1_imp_weak : Question1 → Question1Weak := by
  rintro ⟨ε, hε, N₀, h⟩
  exact ⟨ε, hε, fun M => ⟨max N₀ M, le_max_right _ _, h _ (le_max_left _ _)⟩⟩

/-- A positive-density construction for the second condition gives a negative answer to Question 2. -/
@[category test, AMS 11]
theorem positiveDensity2_imp_not_question2 : PositiveDensity2 → ¬ Question2 := by
  rintro ⟨c, hc, N₀, h⟩ hQ
  obtain ⟨N₁, hN₁⟩ := hQ (c / 2) (by positivity)
  set N := max N₀ N₁ + 1
  obtain ⟨A, hAsub, hAadm, hAcard⟩ := h N (by omega)
  have h2 := hN₁ N (by omega) A hAsub hAadm
  have hNpos : (0 : ℝ) < N := by positivity
  nlinarith

end Erdos327
