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

public import FormalConjecturesForMathlib.Combinatorics.AP.Basic
public import Mathlib.Data.Finset.Prod

/-!
# Counting finite arithmetic progressions
-/

@[expose] public section

/--
The number of nontrivial `k`-term arithmetic progressions in a finite set `A`, each progression
`a, a + d, …, a + (k - 1) d` (with `d > 0`) counted once via its first two terms for `2 ≤ k`. Singleton progressions are counted
by their sole element; by convention, there are zero progressions of length zero.
-/
noncomputable def Finset.apCount (k : ℕ) (A : Finset ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then A.card else
    ((A ×ˢ A).filter fun p : ℕ × ℕ ↦
      p.1 < p.2 ∧ ∀ i < k, p.1 + i * (p.2 - p.1) ∈ A).card

/-- `A` contains a nontrivial `ℓ`-term arithmetic progression. Lengths zero and one are
trivial, as in `Set.IsAPOfLengthFree`; uses in Erdős179 have `2 ≤ ℓ`. -/
def Finset.ContainsNontrivialAP (ℓ : ℕ) (A : Finset ℕ) : Prop :=
  ¬ (A : Set ℕ).IsAPOfLengthFree ℓ

@[simp] theorem Finset.apCount_zero (A : Finset ℕ) : Finset.apCount 0 A = 0 := by
  simp [Finset.apCount]

@[simp] theorem Finset.apCount_one (A : Finset ℕ) : Finset.apCount 1 A = A.card := by
  simp [Finset.apCount]

/-- The empty set has no nonempty progressions. -/
@[simp] theorem Finset.apCount_empty (k : ℕ) : Finset.apCount k ∅ = 0 := by
  simp [Finset.apCount]

/-- There are no nontrivial progressions of length zero. -/
@[simp] theorem Finset.not_containsNontrivialAP_zero (A : Finset ℕ) :
    ¬ Finset.ContainsNontrivialAP 0 A := by
  simp [Finset.ContainsNontrivialAP, Set.isAPOfLengthFree_zero]

/-- There are no nontrivial progressions of length one. -/
@[simp] theorem Finset.not_containsNontrivialAP_one (A : Finset ℕ) :
    ¬ Finset.ContainsNontrivialAP 1 A := by
  simp [Finset.ContainsNontrivialAP, Set.isAPOfLengthFree_one]
