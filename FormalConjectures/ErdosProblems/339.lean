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
# Erdős Problem 339

*References:*
- [erdosproblems.com/339](https://www.erdosproblems.com/339)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [HHP03] Hegyvári, N., Hennecart, F. and Plagne, A., *A proof of two Erdős' conjectures on
  restricted addition and further results*. J. Reine Angew. Math. 560 (2003), 199-220.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Erdos339

/-- The sums of exactly $r$ distinct elements of $A$. -/
def distinctSums (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, S.card = r ∧ (↑S : Set ℕ) ⊆ A ∧ ∑ s ∈ S, s = n}

/--
Let $A\subseteq \mathbb{N}$ be a basis of order $r$. Must the set of integers representable as
the sum of exactly $r$ distinct elements from $A$ have positive lower density?

The answer to both questions is yes, as proved by Hegyvári, Hennecart, and Plagne [HHP03].

Here a basis of order $r$ represents every sufficiently large integer using at most $r$
summands, as in the website's definitions. Repetitions are allowed in the basis hypothesis.
-/
@[category research solved, AMS 5 11]
theorem erdos_339 : answer(True) ↔
    ∀ (A : Set ℕ) (r : ℕ), (∀ᶠ n in atTop, ∃ k ≤ r, n ∈ k • A) →
      0 < (distinctSums r A).lowerDensity := by
  sorry

/--
Erdős and Graham also ask whether if the set of integers which are the sum of $r$ elements
from $A$ has positive upper density then must the set of integers representable as the sum
of exactly $r$ distinct elements have positive upper density?

The answer to both questions is yes, as proved by Hegyvári, Hennecart, and Plagne [HHP03].
-/
@[category research solved, AMS 5 11]
theorem erdos_339.variants.upper_density : answer(True) ↔
    ∀ (A : Set ℕ) (r : ℕ), 0 < (r • A).upperDensity →
      0 < (distinctSums r A).upperDensity := by
  sorry

/-- If every sufficiently large integer is a sum of exactly $r$ elements of $A$, then the
sums of exactly $r$ distinct elements of $A$ have positive lower density. -/
@[category research solved, AMS 5 11]
theorem erdos_339.variants.exact_order :
    ∀ (A : Set ℕ) (r : ℕ), A.IsAsymptoticAddBasisOfOrder r →
      0 < (distinctSums r A).lowerDensity := by
  intro A r hA
  apply (erdos_339.mp trivial) A r
  exact (Set.isAsymptoticAddBasisOfOrder_iff_atTop.mp hA).mono fun _ hn ↦ ⟨r, le_rfl, hn⟩

@[category test, AMS 5 11]
theorem distinctSums_zero (A : Set ℕ) : distinctSums 0 A = {0} := by
  ext n
  simp [distinctSums]

@[category test, AMS 5 11]
theorem distinctSums_one (A : Set ℕ) : distinctSums 1 A = A := by
  ext n
  constructor
  · rintro ⟨S, hS, hSA, hsum⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
    simp only [Finset.sum_singleton] at hsum
    subst n
    exact hSA (by simp)
  · intro hn
    exact ⟨{n}, by simp, by simpa, by simp⟩

@[category test, AMS 5 11]
theorem distinctSums_no_repetitions : 2 ∉ distinctSums 2 {1} := by
  rintro ⟨S, hS, hSA, -⟩
  have hsub : S ⊆ {1} := fun x hx ↦ by simpa using hSA hx
  have := Finset.card_le_card hsub
  simp at this
  omega

@[category test, AMS 5 11]
theorem distinctSums_pair : 5 ∈ distinctSums 2 {1, 2, 3} := by
  refine ⟨{2, 3}, by decide, ?_, by decide⟩
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp

end Erdos339
