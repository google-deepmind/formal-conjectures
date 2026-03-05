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
# Erdős Problem 909

For every $n \geq 2$, is there a topological space of covering dimension $n$ whose square also
has covering dimension $n$? Proved by Anderson and Keisler.

*Reference:* [erdosproblems.com/909](https://www.erdosproblems.com/909)

[AnKe67] Anderson, R. D. and Keisler, J. E., _An example in dimension theory_, 1967.
-/

open TopologicalSpace Set Classical

namespace Erdos909

/-- A topological space has covering dimension at most $n$ if every finite open
    cover has a finite open refinement of order at most $n + 1$, meaning every
    point belongs to at most $n + 1$ sets of the refinement. -/
def coveringDimLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    ∃ (κ : Type) (_ : Fintype κ) (V : κ → Set X),
      (∀ k, IsOpen (V k)) ∧
      (⋃ k, V k) = univ ∧
      (∀ k, ∃ i, V k ⊆ U i) ∧
      ∀ x : X, (Finset.univ.filter (fun k => x ∈ V k)).card ≤ n + 1

/-- A topological space has covering dimension exactly $n$. -/
def hasCoveringDim (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  coveringDimLE X n ∧ ∀ m : ℕ, m < n → ¬coveringDimLE X m

/--
Erdős Problem 909 (proved by Anderson and Keisler [AnKe67]):

For every $n \geq 2$, there exists a topological space $S$ of covering dimension $n$
such that $S \times S$ also has covering dimension $n$.
-/
@[category research solved, AMS 54]
theorem erdos_909 : answer(True) ↔
    ∀ n : ℕ, n ≥ 2 → ∃ (S : Type) (_ : TopologicalSpace S),
      hasCoveringDim S n ∧ hasCoveringDim (S × S) n := by
  sorry

end Erdos909
