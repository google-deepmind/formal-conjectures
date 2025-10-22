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

/-!
# A conjecture by Margulis on matrix groups

*Reference:* [arxiv/2504.17644](https://arxiv.org/pdf/2504.17644v3)
**Bounded diagonal orbits in homogeneous spaces over function fields**
by *Qianlin Huang, Ronggang Shi*
-/

section MatrixGroupConjecture

open Matrix SpecialLinearGroup
open scoped MatrixGroups Polynomial

section

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

-- This instance can be made more general (this is being done in
-- https://github.com/leanprover-community/mathlib4/pull/27596)
instance : TopologicalSpace (SpecialLinearGroup n ℝ) :=
  inferInstanceAs (TopologicalSpace { A : Matrix n n ℝ // A.det = 1 })

end


/-
Let `D` be the diagonal group of `SL_n(R)` where `n ≥ 3`. Then any relatively compact `D`-orbit in
`SL_n(R)/ SLn(Z)` is closed. -/
@[category research open, AMS 11 15 22]
theorem conjecture_1_1 {n : ℕ} (hn : 3 ≤ n)
    (g : SL(n, ℝ) ⧸ Subgroup.map (map (Int.castRingHom ℝ)) ⊤)
    (hg : IsCompact <| closure (MulAction.orbit (diagonalSubgroup (Fin n) ℝ) g)) :
    IsClosed <| MulAction.orbit (diagonalSubgroup (Fin n) ℝ) g :=
  sorry

-- TODO(Paul-Lez): add main theorem from the paper.

end MatrixGroupConjecture
