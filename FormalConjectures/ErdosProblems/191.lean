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
# Erdős Problem 191

*Reference:* [erdosproblems.com/191](https://www.erdosproblems.com/191)

A 2-colouring of pairs is modeled as a `SimpleGraph` on $\mathbb{N}$ (edges = colour 1,
non-edges = colour 2). A monochromatic set is a clique in either $G$ or its
complement $G^c$.

The answer is yes, proved by Rödl [Ro03]. Conlon, Fox, and Sudakov [CFS13]
proved the optimal quantitative bound: in any 2-colouring one can find such $X$
with $\sum 1/\log x \geq c \cdot \log \log \log n$.

[ErGr79] Erdős, P. and Graham, R., 1979.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).

[Er81] Erdős, P., 1981.

[Er82e] Erdős, P., 1982.

[Ro03] Rödl, V., 2003.

[CFS13] Conlon, D., Fox, J., and Sudakov, B., 2013.
-/

open SimpleGraph Real BigOperators

namespace Erdos191

/--
Erdős Problem 191 [ErGr79, ErGr80, Er81, Er82e]:
For any $C > 0$, if $n$ is sufficiently large (depending on $C$), then in any
2-colouring of the pairs from $\{2, \ldots, n\}$, there exists a monochromatic
set $X \subseteq \{2, \ldots, n\}$ with $\sum_{x \in X} 1 / \log x \geq C$.
-/
@[category research solved, AMS 5]
theorem erdos_191 :
    answer(True) ↔
      ∀ C : ℝ, C > 0 →
        ∃ N : ℕ, ∀ n ≥ N,
          ∀ G : SimpleGraph ℕ,
            ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
              (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
              C ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) := by
  sorry

end Erdos191
