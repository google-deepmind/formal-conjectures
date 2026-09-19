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

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Length

/-!
# Serre's intersection multiplicity

For a commutative ring `R` and `R`-modules `M`, `N`, this file defines Serre's intersection
multiplicity
$$\chi(M, N) = \sum_{i \ge 0} (-1)^i \ell_R(\operatorname{Tor}_i^R(M, N)),$$
using `CategoryTheory.Tor` on `ModuleCat R`.

The definition is meaningful when `R` is a regular local ring, `M` and `N` are finitely generated
and `M ⊗[R] N` has finite length: then `Tor_i` vanishes for `i > dim R`, so the sum is finite, and
every `Tor_i` has finite length, so `ENat.toNat` truncates nothing.

## Main declarations

- `Module.intersectionMultiplicity R M N`: the alternating sum above.
- `Module.intersectionMultiplicity_of_projective`: if `N` is projective, `χ(M, N) = ℓ(M ⊗ N)`.
- `Module.intersectionMultiplicity_self_self`: over a field `k`, `χ(k, k) = 1`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory TensorProduct

universe u

namespace Module

variable (R : Type u) [CommRing R]
  (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
The **intersection multiplicity** of two modules `M` and `N` over a commutative ring `R`,
$$\chi(M, N) = \sum_{i \ge 0} (-1)^i \ell_R(\operatorname{Tor}_i^R(M, N)).$$
Here `Tor` is `CategoryTheory.Tor` on `ModuleCat R`, the sum is a `finsum` over `ℕ`, and the
length of each Tor module is converted to a natural number by `ENat.toNat`.
-/
noncomputable def intersectionMultiplicity : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
    (Module.length R (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R N))).toNat

variable {R M N}

/-- If `N` is projective, only `Tor₀(M, N) = M ⊗ N` contributes to `χ(M, N)`. -/
theorem intersectionMultiplicity_of_projective [Module.Projective R N] :
    intersectionMultiplicity R M N = (Module.length R (M ⊗[R] N)).toNat := by
  unfold intersectionMultiplicity
  rw [finsum_eq_single _ 0]
  · have e : ((Tor (ModuleCat.{u} R) 0).obj (ModuleCat.of R M)).obj (ModuleCat.of R N) ≅
        ModuleCat.of R M ⊗ ModuleCat.of R N :=
      ((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app _
    rw [pow_zero, one_mul, e.toLinearEquiv.length_eq]
    rfl
  · intro i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have : Subsingleton (((Tor (ModuleCat.{u} R) (n + 1)).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R N)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_Tor_succ_of_projective (ModuleCat.{u} R) (ModuleCat.of R M) (ModuleCat.of R N) n)
    simp

/-- Normalisation: over a field `k`, `χ(k, k) = 1`. -/
theorem intersectionMultiplicity_self_self (k : Type u) [Field k] :
    intersectionMultiplicity k k k = 1 := by
  rw [intersectionMultiplicity_of_projective, (TensorProduct.lid k k).length_eq,
    Module.length_eq_one]
  rfl

end Module
