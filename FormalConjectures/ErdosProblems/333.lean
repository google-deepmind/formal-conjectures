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
# Erdős Problem 333

*Reference:* [erdosproblems.com/333](https://www.erdosproblems.com/333)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathématique (1980).

[ErNe77] Erdős, P. and Newman, D.J.
-/

open scoped Classical

namespace Erdos333

/--
The upper density of $A \subseteq \mathbb{N}$:
$$\overline{d}(A) = \limsup_{N \to \infty} |A \cap \{0, 1, \ldots, N-1\}| / N$$
-/
noncomputable def upperDensity333 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem 333 [ErGr80] (DISPROVED):

Let $A \subseteq \mathbb{N}$ be a set of density zero. Does there exist a set
$B \subseteq \mathbb{N}$ such that $A \subseteq B + B$ and
$|B \cap \{1, \ldots, N\}| = o(N^{1/2})$?

Here $B + B = \{b_1 + b_2 \mid b_1, b_2 \in B\}$ is the sumset of $B$ with itself, and
$o(N^{1/2})$ means that $|B \cap \{1, \ldots, N\}| / N^{1/2} \to 0$ as $N \to \infty$.

Erdős and Newman [ErNe77] proved this is true when $A$ is the set of squares.
However, Theorem 2 of [ErNe77] already implies a negative answer to this
problem in general, though this was overlooked by Erdős and Graham.
-/
@[category research solved, AMS 5 11]
theorem erdos_333 : answer(False) ↔
    ∀ A : Set ℕ, upperDensity333 A = 0 →
      ∃ B : Set ℕ,
        A ⊆ Set.image2 (· + ·) B B ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ) ≤ ε * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos333
