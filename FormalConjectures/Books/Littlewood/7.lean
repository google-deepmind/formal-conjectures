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

public import FormalConjecturesUtil

/-!
# Littlewood's mutually touching infinite cylinders problem

Littlewood asked whether seven congruent infinite circular cylinders can touch
pairwise in [Lit68, Problem 7, p. 20], as quoted in [BLR15, Section 1].
This file states the maximum-seven formulation of the cylinder problem, given in
[Ko25, Introduction]: is seven the maximum number of such cylinders in Euclidean
three-space with pairwise disjoint interiors?

After scaling the common radius to $1/2$, the problem is equivalent to asking for
the greatest number of affine lines in Euclidean three-space whose pairwise distances
are one.

*References:*
- [Lit68] J. E. Littlewood, *Some Problems in Real and Complex Analysis*,
  D. C. Heath, 1968, Problem 7, p. 20. The original question is quoted in [BLR15].
- [BLR15] S. Bozóki, T.-L. Lee and L. Rónyai,
  [*Seven mutually touching infinite cylinders*](https://arxiv.org/abs/1308.5164),
  Computational Geometry 48 (2015), 87–93, Section 1.
- [Ko25] J. Koizumi,
  [*A new upper bound for mutually touching infinite cylinders*]
  (https://arxiv.org/abs/2506.19309), Introduction.
-/

@[expose] public section

namespace LittlewoodCylinders

/--
Is seven the greatest number of affine lines in Euclidean three-space whose pairwise
distances are exactly one? This is the normalized form of Littlewood's problem on
mutually touching congruent infinite circular cylinders, as stated in [Ko25].
It includes both seven-cylinder existence and the upper bound of seven.
-/
@[category research solved, AMS 51 52,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/littlewood-cylinders-lean/blob/039541f649f618c8c761201665038539001bddd5/lean/LittlewoodCylindersFC.lean#L210-L224"]
theorem littlewood_cylinders : answer(True) ↔
    IsGreatest
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ |
              ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1}
      7 := by
  sorry

end LittlewoodCylinders
