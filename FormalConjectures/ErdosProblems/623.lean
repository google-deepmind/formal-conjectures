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
import FormalConjectures.Util.ProblemImports

open Filter Real Set
open scoped Cardinal Ordinal

namespace Erdos623

/-!
# Erdős Problem 623

*Reference:* [erdosproblems.com/623](https://www.erdosproblems.com/623)
-/
universe u

/--
Let $X$ be a set of cardinality $\aleph_\omega$ and $f$ be a function from the finite subsets of
$X$ to $X$ such that $f(A)\not\in A$ for all $A$. Must there exist an infinite $Y\subseteq X$
that is independent - that is, for all finite $B\subset Y$ we have $f(B)\not\in Y$?
-/
@[category research open, AMS 3]
theorem erdos_623 : (∀ (X : Type u) (hX : #X = ℵ_ ω)
    (f : Finset X → X), (∀ A : Finset X, f A ∉ A) →
    (∃ Y : Set X, Set.Infinite Y ∧ (∀ (B : Finset X), ↑B ⊆ Y → f B ∉ Y))) ↔ answer(sorry) := by
  sorry

-- TODO(firsching): formalize the statement about X < ℵ_ω

end Erdos623
