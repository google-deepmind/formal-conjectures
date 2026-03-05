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
# Erdős Problem 1090

*Reference:* [erdosproblems.com/1090](https://www.erdosproblems.com/1090)

Let $k \geq 3$. Does there exist a finite set $A \subset \mathbb{R}^2$ such that, in any
2-colouring of $A$, there exists a line which contains at least $k$ points from $A$, and all the
points of $A$ on the line have the same colour?

[Er75f] Erdős, P., *Problems and results on combinatorial number theory III*.
-/

namespace Erdos1090

/--
Let $k \geq 3$. Does there exist a finite set $A \subset \mathbb{R}^2$ such that, in any
2-colouring of $A$, there exists a line which contains at least $k$ points from $A$, and all the
points of $A$ on the line have the same colour?

The answer is yes. Erdős [Er75f] notes that Graham and Selfridge proved the
case $k = 3$. Hunter observed that for sufficiently large $n$, a generic projection
of $[k]^n$ into $\mathbb{R}^2$ has this property, by the Hales–Jewett theorem.
-/
@[category research solved, AMS 5 51]
theorem erdos_1090 : answer(True) ↔ ∀ (k : ℕ), k ≥ 3 →
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      ∀ c : EuclideanSpace ℝ (Fin 2) → Fin 2,
        ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ L.direction = 1 ∧
          k ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (A : Set _) ∧ p ∈ L} ∧
          ∃ color : Fin 2, ∀ p ∈ (A : Set _), p ∈ L → c p = color := by
  sorry

end Erdos1090
