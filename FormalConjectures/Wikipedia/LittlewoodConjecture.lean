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
# Littlewood conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Littlewood_conjecture)
-/

open Filter

-- TODO(mercuris): This is a norm on ℝ/ℤ, show this?
/--
The distance to the nearest integer is the function
$\||x\|| := \min(|x - \lfloor x \rfloor|, |x - \lceil x \rceil|)$.
-/
noncomputable abbrev distToNearestInt (x : ℝ) : ℝ := |x - round x|

/--
For any two real numbers $\alpha$ and $\beta$,
$$
  \liminf_{n\to\infty} n\||n\alpha\||\||n\beta\|| = 0
$$
where $\||nx\|| := \min(|x - \lfloor x \rfloor|, |x - \lceil x \rceil|)$ is the distance
to the nearest integer.
-/
@[category research solved, AMS 11]
theorem littlewood_conjecture (α β : ℝ) :
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0 := by
  sorry

section MatrixGroupConjecture

open Matrix
open scoped MatrixGroups

section
variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

-- This instance can be made more general (this is being done in https://github.com/leanprover-community/mathlib4/pull/27596)
instance : TopologicalSpace (SpecialLinearGroup n ℝ) :=
  inferInstanceAs (TopologicalSpace { A : Matrix n n ℝ // A.det = 1 })

end

open Pointwise

/-- `SL_n(ℤ)`, viewed as a subgroup of `SL_n(ℝ)`-/
private abbrev SpecialLinearGroupIntSubgroup (n : ℕ) : Subgroup SL(n, ℝ) :=
  (⊤ : Subgroup _).map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-
Formalisation note: the original wiki page seems uses left quotients, but it seems (based on
the existing litterature that one should be taking right quotients. This is what has been done
here).
-/

/-- Let `n ≥ 3`, `G = SL_n(ℝ)` and `Γ = SL_n(ℤ)`, and the subgroup `D` of diagonal matrices in `G`.

Conjecture: for any `g` in `Γ\G` such that `Dg` is relatively compact (in `Γ\G`), then `Dg` is closed.-/
@[category research open, AMS 11 15 22]
theorem matrix_group_conjecture {n : ℕ} (hn : 3 ≤ n) (g : MulOpposite SL(n, ℝ))
    (D : Set (MulOpposite SL(n, ℝ) ⧸
      ((⊤ : Subgroup _).map (SpecialLinearGroup.map (Int.castRingHom ℝ))).op))
    (D_def : D = QuotientGroup.mk '' (Matrix.SpecialLinearGroup.diagonalSubgroup _ _).op.carrier)
    (hg : IsCompact <| closure (g • D)) : IsClosed (g • D) :=
  sorry

end MatrixGroupConjecture
