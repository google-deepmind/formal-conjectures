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
# Erdős Problem 363

*Reference:* [erdosproblems.com/363](https://www.erdosproblems.com/363)

Is it true that there are only finitely many collections of disjoint intervals
$I_1, \ldots, I_n$ of consecutive integers with $|I_i| \geq 4$ for all $i$, such that
$\prod_i \prod_{m \in I_i} m$ is a perfect square?

This was disproved:
- [Ul05] Ulas, M., _On products of disjoint blocks of consecutive integers_.
  Enseignement Mathématique (2) (2005), 331–334.
- [BaBe07] Bauer, M., Bennett, M. A., _On a question of Erdős and Graham_.
  Enseignement Mathématique (2) (2007), 259–264.
- [BeVL12] Bennett, M. A., Van Luijk, R., _Squares from blocks of consecutive integers:
  a problem of Erdős and Graham_. Indagationes Mathematicae (N.S.) (2012), 123–127.
-/

namespace Erdos363

/--
Erdős Problem 363 (Disproved by Bauer–Bennett [BaBe07]):

Are there only finitely many triples $(a, b, c)$ of positive natural numbers with
$a + 4 \leq b$ and $b + 4 \leq c$ (so the three intervals of four consecutive integers
starting at $a$, $b$, $c$ are pairwise disjoint) such that the product of all $12$ elements
is a perfect square? The answer is no.
-/
@[category research solved, AMS 11]
theorem erdos_363 : answer(False) ↔
    Set.Finite {t : ℕ × ℕ × ℕ |
      0 < t.1 ∧ t.1 + 4 ≤ t.2.1 ∧ t.2.1 + 4 ≤ t.2.2 ∧
      IsSquare ((∏ m ∈ Finset.Icc t.1 (t.1 + 3), m) *
                (∏ m ∈ Finset.Icc t.2.1 (t.2.1 + 3), m) *
                (∏ m ∈ Finset.Icc t.2.2 (t.2.2 + 3), m))} := by
  sorry

end Erdos363
