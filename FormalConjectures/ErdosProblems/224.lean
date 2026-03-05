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
# Erdős Problem 224

*Reference:* [erdosproblems.com/224](https://www.erdosproblems.com/224)

If $A \subseteq \mathbb{R}^d$ is any set of $2^d + 1$ points then some three
points in $A$ determine an obtuse angle.

## Known results

- For $d = 2$ this is trivial.
- For $d = 3$ there is an unpublished proof by Kuiper and Boerdijk.
- The general case was proved by Danzer and Grünbaum [DaGr62].

[DaGr62] Danzer, L. and Grünbaum, B., _Über zwei Probleme bezüglich konvexer
Körper von P. Erdős und von V.L. Klee_, Math. Z. 79 (1962), 95–99.
-/

namespace Erdos224

/--
Erdős Problem 224 (Danzer–Grünbaum [DaGr62]):
Any set of at least $2^d + 1$ points in $\mathbb{R}^d$ contains three distinct
points $a$, $b$, $c$ such that the angle at $b$ is obtuse
(i.e., $\langle a - b, c - b \rangle < 0$).
-/
@[category research solved, AMS 52]
theorem erdos_224 (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : 2 ^ d + 1 ≤ A.card) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      @inner ℝ _ _ (a - b) (c - b) < 0 := by
  sorry

end Erdos224
