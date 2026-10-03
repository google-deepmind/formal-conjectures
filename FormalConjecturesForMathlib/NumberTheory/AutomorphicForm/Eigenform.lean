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

public import FormalConjecturesForMathlib.NumberTheory.Hecke.AdelicAction

@[expose] public section

/-!
# Automorphic eigenforms

An **automorphic eigenform** for `GL m / ℚ`: an automorphic form in the sense of
Borel-Jacquet which, for all but finitely many primes `p`, is unramified at `p` and a
simultaneous eigenvector of the spherical Hecke operators `T_{p,i}` for all `i`.

This is a deliberately ad hoc definition, made at the level of a single form rather than of
an automorphic representation: no multiplicity one, no decomposition into local components,
and no admissibility enter. What it retains is exactly the data needed to state Langlands
functoriality for general linear groups on Satake parameters: at each unramified prime the
eigensystem `a : Fin (m + 1) → ℂ`, unique for a given form (`HasHeckeEigensystemAt.unique`),
whose Hecke polynomial has the `m` Satake parameters as roots.

## Main declarations

* `HasHeckeEigensystemAt`: the form is unramified at `p` and an eigenvector of every
  `T_{p,i}`, with eigenvalue system `a`.
* `IsAutomorphicEigenform`: the form has a Hecke eigensystem at all but finitely many `p`.
* `HasHeckeEigensystemAt.unique`: the eigensystem at `p` is unique.
* `HasHeckeEigensystemAt.card_satakeParameters`: at an unramified prime an eigenform has
  exactly `m` Satake parameters, counted with multiplicity.
-/

namespace Matrix.GeneralLinearGroup

open scoped IsDedekindDomain.FiniteAdeleRing

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

variable {m : ℕ}

/-- The form `f` has **Hecke eigensystem `a` at `p`**: it is unramified at `p`, and for every
`i` it is an eigenvector of the spherical Hecke operator `T_{p,i}` with eigenvalue `a i`. -/
def HasHeckeEigensystemAt (p : Nat.Primes) (f : automorphicForms (Fin m))
    (a : Fin (m + 1) → ℂ) : Prop :=
  ∃ hf : IsUnramifiedAt p f,
    IsSphericalEigenvector (localRepresentation p)
      (fun _ ha => PadicInt.finite_quotient_span_singleton ha) (padicUnit p) ⟨f, hf⟩ a

/-- **Automorphic eigenform** (ad hoc): an automorphic form which, for all but finitely many
primes `p`, is unramified at `p` and a simultaneous eigenvector of the spherical Hecke
operators `T_{p,i}` for all `i`. The form is automatically nonzero, an eigenvector being
nonzero by definition. -/
def IsAutomorphicEigenform (f : automorphicForms (Fin m)) : Prop :=
  ∃ S : Finset Nat.Primes, ∀ p ∉ S, ∃ a : Fin (m + 1) → ℂ, HasHeckeEigensystemAt p f a

namespace HasHeckeEigensystemAt

variable {p : Nat.Primes} {f : automorphicForms (Fin m)} {a b : Fin (m + 1) → ℂ}

theorem ne_zero (h : HasHeckeEigensystemAt p f a) : f ≠ 0 := by
  obtain ⟨hf, he⟩ := h
  intro hzero
  exact he.ne_zero (Subtype.ext hzero)

/-- The eigensystem of a form at `p` is unique: eigenvalues of a common nonzero eigenvector
agree. This is what makes the Satake parameters of an eigenform at `p` well defined. -/
theorem unique (ha : HasHeckeEigensystemAt p f a) (hb : HasHeckeEigensystemAt p f b) :
    a = b := by
  have hne := ha.ne_zero
  obtain ⟨hf, hae⟩ := ha
  obtain ⟨hf', hbe⟩ := hb
  -- find a point where `f` does not vanish
  have hval : (f : GL (Fin m) 𝔸ᶠ[ℤ, ℚ] × GL (Fin m) ℝ → ℂ) ≠ 0 :=
    fun h => hne (ZeroMemClass.coe_eq_zero.mp h)
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hval
  funext i
  -- compare the two eigenvalue equations at that point
  have h3 := (hae.eigen i).symm.trans (hbe.eigen i)
  have h4 := congrArg Subtype.val h3
  rw [SetLike.val_smul, SetLike.val_smul] at h4
  have h5 := congrArg Subtype.val h4
  rw [SetLike.val_smul, SetLike.val_smul] at h5
  have h6 := congrFun h5 x
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at h6
  exact mul_right_cancel₀ (by simpa using hx) h6

/-- The eigenvalue of `T_{p,0}` is `1`, so the eigensystem is normalised and its Hecke
polynomial is monic. -/
theorem eigenvalue_zero (h : HasHeckeEigensystemAt p f a) : a 0 = 1 := by
  obtain ⟨hf, he⟩ := h
  exact he.eigenvalue_zero

/-- At an unramified prime an eigenform has exactly `m` Satake parameters, counted with
multiplicity: the roots of the Hecke polynomial of its eigensystem. -/
theorem card_satakeParameters (h : HasHeckeEigensystemAt p f a) :
    Multiset.card (Satake.satakeParameters p a) = m :=
  Satake.card_satakeParameters h.eigenvalue_zero

end HasHeckeEigensystemAt

end Matrix.GeneralLinearGroup
