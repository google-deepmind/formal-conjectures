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

namespace Erdos355

/--
Is there a lacunary sequence $A\subseteq \mathbb{N}$ (so that $A=\{a_1 < \cdots\}$ and
there exists some $\lambda > 1$ such that $a_{n+1}/a_n\geq \lambda$ for all $n\geq 1$) such that
\[\left\{ \sum_{a\in A'}\frac{1}{a} : A'\subseteq A\textrm{ finite}\right\}\]
contain all rationals in some open interval?
-/
@[category research open, AMS 11]
theorem erdos_355 :
    (∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Set.Ioo u v →
      q ∈  {(∑ a ∈ A', (1 / a : ℚ)) | (A' : Finset ℕ) (_ : A'.toSet ⊆ Set.range A)})
    ↔ answer(sorry) := by
  sorry


end Erdos355
