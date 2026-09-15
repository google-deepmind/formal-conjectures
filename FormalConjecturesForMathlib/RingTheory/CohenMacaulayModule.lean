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

public import FormalConjecturesForMathlib.RingTheory.SystemOfParameters

/-!
# Small and big Cohen-Macaulay modules

Let `R` be a local ring. A *small Cohen-Macaulay module*, also called a maximal Cohen-Macaulay
module, is a finitely generated nonzero `R`-module `M` such that some system of parameters of `R`
is a regular sequence on `M`. A *balanced big Cohen-Macaulay module* is an `R`-module `W`, not
necessarily finitely generated, with `m • W ≠ W` and such that every system of parameters of `R`
is a regular sequence on `W`. Over a Noetherian local ring the two notions agree for finitely
generated modules.

Both definitions are only intended for Noetherian local rings, where systems of parameters exist.

## Main declarations

- `Module.IsSmallCohenMacaulay R M`: `M` is a small Cohen-Macaulay `R`-module.
- `Module.IsBalancedBigCohenMacaulay R W`: `W` is a balanced big Cohen-Macaulay `R`-module.
-/

@[expose] public section

open IsLocalRing

namespace Module

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/--
A *small Cohen-Macaulay module* over a local ring `R` is a finitely generated `R`-module `M`,
necessarily nonzero, such that some system of parameters of `R` is a regular sequence on `M`.
Such a module is also called a maximal Cohen-Macaulay module. Nonzeroness is automatic, see
`Module.IsSmallCohenMacaulay.nontrivial`.
-/
structure IsSmallCohenMacaulay : Prop where
  /-- A small Cohen-Macaulay module is finitely generated. -/
  finite : Module.Finite R M
  /-- Some system of parameters of `R` is a regular sequence on `M`. -/
  exists_isRegular : ∃ rs, IsSystemOfParameters R rs ∧ RingTheory.Sequence.IsRegular M rs

/--
A *balanced big Cohen-Macaulay module* over a local ring `R` is an `R`-module `M`, not necessarily
finitely generated, with `m • M ≠ M` and such that every system of parameters of `R` is a regular
sequence on `M`.

Part of the literature calls this simply a big Cohen-Macaulay module, and reserves the weaker
condition that *some* system of parameters is a regular sequence for that name. Over a Noetherian
local ring the field `smul_top_ne_top` follows from `isRegular`, see
`Module.smul_top_ne_top_of_isRegular`.
-/
structure IsBalancedBigCohenMacaulay : Prop where
  /-- The maximal ideal does not act by the identity on the module. -/
  smul_top_ne_top : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤
  /-- Every system of parameters of `R` is a regular sequence on `M`. -/
  isRegular : ∀ rs, IsSystemOfParameters R rs → RingTheory.Sequence.IsRegular M rs

variable {R M}

/--
A small Cohen-Macaulay module is nonzero: a regular sequence on `M` is one for which `M` is not
killed by the ideal it generates.
-/
theorem IsSmallCohenMacaulay.nontrivial (h : IsSmallCohenMacaulay R M) : Nontrivial M := by
  obtain ⟨rs, -, hrs⟩ := h.exists_isRegular
  by_contra hM
  rw [not_nontrivial_iff_subsingleton] at hM
  exact hrs.top_ne_smul (@Subsingleton.elim _ ((Submodule.subsingleton_iff R).mpr hM) _ _)

/--
Over a Noetherian local ring, `m • M ≠ M` follows from the regularity of a single system of
parameters, because the ideal that a system of parameters generates contains a power of the
maximal ideal.
-/
theorem smul_top_ne_top_of_isRegular [IsNoetherianRing R] {rs : List R}
    (hrs : IsSystemOfParameters R rs) (h : RingTheory.Sequence.IsRegular M rs) :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  intro hm
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrs.radical_eq.ge
    (IsNoetherian.noetherian _)
  have key : ∀ k : ℕ, (maximalIdeal R ^ k) • (⊤ : Submodule R M) = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hm, ih]
  exact h.top_ne_smul (le_antisymm ((key n).ge.trans (Submodule.smul_mono hn le_rfl)) le_top)

/-- Over a field `K`, the module `K` is a small Cohen-Macaulay module. -/
theorem isSmallCohenMacaulay_self (K : Type*) [Field K] : IsSmallCohenMacaulay K K where
  finite := inferInstance
  exists_isRegular := ⟨[], isSystemOfParameters_nil K, RingTheory.Sequence.IsRegular.nil K K⟩

end Module
