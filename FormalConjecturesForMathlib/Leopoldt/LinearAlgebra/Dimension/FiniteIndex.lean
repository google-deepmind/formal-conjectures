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
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Rank is insensitive to a torsion quotient

Over a commutative domain, if `N ≤ N'` and some nonzero scalar `c` carries `N'` into `N`, then
`N` and `N'` have the same rank: the multiplication-by-`c` map `N' → N` has torsion kernel, so
zero-rank kernel, and rank-nullity does the rest.

This is the "rank does not see finite index" principle: the archetypal application is a subgroup
of finite index `c` inside a `ℤ_p`-module, where `c • N' ⊆ N` holds automatically.
-/

public section

/-- If `N ≤ N'` and `c • N' ⊆ N` for some nonzero `c` in a domain, then `N` and `N'` have the
same rank. -/
theorem rank_eq_of_le_of_smul_le {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] {N N' : Submodule R M} (h : N ≤ N') {c : R} (hc : c ≠ 0)
    (h' : ∀ y ∈ N', c • y ∈ N) : Module.rank R N = Module.rank R N' := by
  refine le_antisymm (Submodule.rank_mono h) ?_
  set f : N' →ₗ[R] N := LinearMap.codRestrict N (c • N'.subtype) (fun y ↦ h' y y.2) with hf
  have hker : Module.rank R (LinearMap.ker f) = 0 := by
    refine rank_eq_zero_iff.2 fun x ↦ ⟨c, hc, ?_⟩
    have hx : f x = 0 := x.2
    have hcx : (c • (x : M)) = 0 := by
      simpa [hf, LinearMap.codRestrict] using congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext hcx)
  calc Module.rank R N' = Module.rank R (N' ⧸ LinearMap.ker f) + Module.rank R (LinearMap.ker f) :=
        (rank_quotient_add_rank_of_isDomain _).symm
    _ = Module.rank R (LinearMap.range f) := by
        rw [hker, add_zero, (f.quotKerEquivRange).rank_eq]
    _ ≤ Module.rank R N := Submodule.rank_le _
