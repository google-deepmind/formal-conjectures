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
module

public import Mathlib

/-!
# Erdős Problem 3

*Reference:* [erdosproblems.com/3](https://www.erdosproblems.com/3)

This is the Erdős–Turán conjecture on arithmetic progressions, which is an open problem.
The `FormalConjecturesUtil` library is not available in this project, so the notion
`Set.IsAPOfLength` is reproduced here (following the Formal Conjectures definition), and the
`answer(sorry)` placeholder is replaced by the conjectured answer "yes".
-/

@[expose] public section

namespace Set

variable {α : Type*} [AddCommMonoid α]

/-- `s` is an arithmetic progression of length `l` with first term `a` and common difference
`d`. -/
def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {x | ∃ n : ℕ, (n : ℕ∞) < l ∧ x = a + n • d}

/-- `s` is an arithmetic progression of length `l`. -/
def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

end Set

namespace Erdos3

/-- The statement of Erdős Problem 3 (the Erdős–Turán conjecture). -/
def Erdos3Statement : Prop :=
  ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k

/--
If $A \subset \mathbb{N}$ has $\sum_{n \in A}\frac 1 n = \infty$, then must $A$ contain arbitrarily
long arithmetic progressions?

This is open; the conjectured answer is "yes". Left unproved.
-/
theorem erdos_3 : Erdos3Statement := by
  sorry

/-- The `k`-term progression `a, a + d, …, a + (k-1)d` with `d > 0` is an AP of length `k`. -/
theorem isAPOfLength_range (a d k : ℕ) (hd : 0 < d) :
    ({x | ∃ n : ℕ, (n : ℕ∞) < (k : ℕ∞) ∧ x = a + n • d} : Set ℕ).IsAPOfLength k := by
  refine ⟨a, d, ?_, rfl⟩
  have : ({x | ∃ n : ℕ, (n : ℕ∞) < (k : ℕ∞) ∧ x = a + n • d} : Set ℕ) =
      (fun n => a + n * d) '' (Set.Iio k) := by
    ext x; simp [Nat.cast_lt, eq_comm]
  rw [this, ENat.card_image_of_injective]
  · simp
  · intro m n h; simpa [hd.ne'] using h

/-- Sanity check of the formalization: if `A` contains an infinite arithmetic progression
`a, a + d, a + 2d, …` with `d > 0`, then `A` contains arbitrarily long arithmetic progressions. -/
theorem erdos_3_of_infinite_AP (A : Set ℕ) (a d : ℕ) (hd : 0 < d)
    (hA : ∀ n : ℕ, a + n * d ∈ A) :
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  refine Filter.Frequently.of_forall fun k => ⟨_, ?_, isAPOfLength_range a d k hd⟩
  rintro x ⟨n, -, rfl⟩
  simpa using hA n

end Erdos3

