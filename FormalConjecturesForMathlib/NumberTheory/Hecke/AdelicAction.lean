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

public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet
public import FormalConjecturesForMathlib.NumberTheory.Hecke.GeneralLinearGroup
public import FormalConjecturesForMathlib.NumberTheory.Hecke.Satake
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

@[expose] public section

/-!
# The spherical Hecke operators at `p` acting on automorphic forms

The local-to-global layer: the embedding `GL n K_v →* GL n 𝔸ᶠ` placing a local matrix at the
place `v` and the identity matrix at every other place, its specialisation
`GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ]`, and the action of the spherical Hecke algebra at `p` on
automorphic forms obtained by pulling back right translation along it. Since `GL n ℤ_[p]` is
a Hecke pair (`Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup_padic`), the spherical
Hecke operators of `FormalConjecturesForMathlib.NumberTheory.Hecke.Satake` then act on the
`GL n ℤ_[p]`-invariant automorphic forms directly, and no Hecke pair inside `GL n 𝔸ᶠ` is
needed.

The embedding is not induced by a ring homomorphism `K_v → 𝔸ᶠ`: placing an element at one
place and zero elsewhere does not preserve `1`. It is multiplicative on matrices because the
off-`v` components are all the identity matrix, whose products are again the identity.

## Main declarations

* `IsDedekindDomain.FiniteAdeleRing.localGL`: the group homomorphism
  `GL n K_v →* GL n 𝔸ᶠ[R, K]` at a place `v` of a Dedekind domain, built from the matrix
  `IsDedekindDomain.FiniteAdeleRing.localMatrix`.
* `Matrix.GeneralLinearGroup.padicToFiniteAdeles`: its specialisation
  `GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ]`, through Mathlib's identification of `ℚ_[p]` with the
  completion of `ℚ` at the height-one prime `(p)` of `ℤ` (`Padic.adicCompletionEquiv`).
* `Matrix.GeneralLinearGroup.localRepresentation` and
  `Matrix.GeneralLinearGroup.IsUnramifiedAt`: right translation on the automorphic forms
  restricted to `GL n ℚ_[p]`, and invariance under (the image of) `GL n ℤ_[p]`.
* `Matrix.GeneralLinearGroup.adelicHeckeT p i`: the spherical Hecke operator `T_{p,i}`, at
  the double coset of `diag (p, …, p, 1, …, 1)` with `i` entries `p`, acting on the
  unramified-at-`p` automorphic forms.
-/

/-! ### The local embedding `GL n K_v →* GL n 𝔸ᶠ` at one place -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Classical in
/-- The adele equal to `x` at `v` and to the image of `y : K` at every other place. -/
noncomputable def singleAt (v : HeightOneSpectrum R) (x : v.adicCompletion K) (y : R) :
    𝔸ᶠ[R, K] :=
  RestrictedProduct.mk
    (Function.update (fun w : HeightOneSpectrum R => (algebraMap R (w.adicCompletion K)) y) v x)
    (by
      filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton v)] with w hw
      have hwv : w ≠ v := by simpa using hw
      simp only [Function.update_of_ne hwv]
      exact coe_mem_adicCompletionIntegers w y)

@[simp]
theorem singleAt_apply_self (v : HeightOneSpectrum R) (x : v.adicCompletion K) (y : R) :
    singleAt v x y v = x := by
  classical
  show Function.update
    (fun w : HeightOneSpectrum R => (algebraMap R (w.adicCompletion K)) y) v x v = x
  simp

open scoped Classical in
@[simp]
theorem singleAt_apply_of_ne {v w : HeightOneSpectrum R} (hw : w ≠ v)
    (x : v.adicCompletion K) (y : R) :
    singleAt v x y w = (algebraMap R (w.adicCompletion K)) y := by
  show Function.update
    (fun u : HeightOneSpectrum R => (algebraMap R (u.adicCompletion K)) y) v x w = _
  simp [Function.update_of_ne hw]

@[simp] theorem mul_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

@[simp] theorem one_apply (v : HeightOneSpectrum R) : (1 : 𝔸ᶠ[R, K]) v = 1 := rfl

@[simp] theorem zero_apply (v : HeightOneSpectrum R) : (0 : 𝔸ᶠ[R, K]) v = 0 := rfl

@[simp] theorem add_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a + b) v = a v + b v := rfl

variable (R K) in
/-- Evaluation of a finite adele at the place `v`, as a ring homomorphism. -/
def evalRingHom (v : HeightOneSpectrum R) : 𝔸ᶠ[R, K] →+* v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  map_sum (evalRingHom R K v) f s

open scoped Classical in
/-- The matrix over `𝔸ᶠ` equal to `M` at `v` and to the identity matrix elsewhere. -/
noncomputable def localMatrix (v : HeightOneSpectrum R)
    (M : Matrix n n (v.adicCompletion K)) : Matrix n n 𝔸ᶠ[R, K] :=
  Matrix.of fun i j => singleAt v (M i j) (if i = j then 1 else 0)

omit [Fintype n] in
@[simp]
theorem localMatrix_apply_self (v : HeightOneSpectrum R) (M : Matrix n n (v.adicCompletion K))
    (i j : n) : (localMatrix v M i j) v = M i j := by
  simp [localMatrix]

omit [Fintype n] in
theorem localMatrix_apply_of_ne {v w : HeightOneSpectrum R} (hw : w ≠ v)
    (M : Matrix n n (v.adicCompletion K)) (i j : n) :
    (localMatrix v M i j) w = (1 : Matrix n n (w.adicCompletion K)) i j := by
  classical
  rw [localMatrix, Matrix.of_apply, singleAt_apply_of_ne hw, Matrix.one_apply]
  split <;> simp

omit [Fintype n] in
theorem localMatrix_one (v : HeightOneSpectrum R) :
    localMatrix v (1 : Matrix n n (v.adicCompletion K)) = 1 := by
  ext i j w
  rcases eq_or_ne w v with rfl | hw
  · rw [localMatrix_apply_self, Matrix.one_apply, Matrix.one_apply,
      apply_ite (fun x : 𝔸ᶠ[R, K] => x w), one_apply, zero_apply]
  · rw [localMatrix_apply_of_ne hw, Matrix.one_apply, Matrix.one_apply,
      apply_ite (fun x : 𝔸ᶠ[R, K] => x w), one_apply, zero_apply]

theorem localMatrix_mul (v : HeightOneSpectrum R)
    (M N : Matrix n n (v.adicCompletion K)) :
    localMatrix v (M * N) = localMatrix v M * localMatrix v N := by
  ext i j w
  rw [Matrix.mul_apply, sum_apply]
  rcases eq_or_ne w v with rfl | hw
  · rw [localMatrix_apply_self, Matrix.mul_apply]
    simp only [mul_apply, localMatrix_apply_self]
  · rw [localMatrix_apply_of_ne hw]
    simp only [mul_apply, localMatrix_apply_of_ne hw]
    rw [← Matrix.mul_apply, one_mul]

/-- **The local embedding of general linear groups**: the group homomorphism
`GL n K_v →* GL n 𝔸ᶠ` placing a local matrix at the place `v` and the identity matrix at
every other place. It is not induced by a ring homomorphism `K_v → 𝔸ᶠ`, but it is
multiplicative because the off-`v` components are all the identity matrix. -/
noncomputable def localGL (v : HeightOneSpectrum R) :
    GL n (v.adicCompletion K) →* GL n 𝔸ᶠ[R, K] where
  toFun g :=
    ⟨localMatrix v g.val, localMatrix v g.inv,
      by rw [← localMatrix_mul, g.val_inv, localMatrix_one],
      by rw [← localMatrix_mul, g.inv_val, localMatrix_one]⟩
  map_one' := Units.ext (localMatrix_one v)
  map_mul' g h := Units.ext (localMatrix_mul v g.val h.val)

@[simp]
theorem coe_localGL (v : HeightOneSpectrum R) (g : GL n (v.adicCompletion K)) :
    (localGL v g : Matrix n n 𝔸ᶠ[R, K]) = localMatrix v (g : Matrix n n (v.adicCompletion K)) :=
  rfl

end IsDedekindDomain.FiniteAdeleRing

/-! ### The `p`-adic points inside the finite-adelic points, and the Hecke action -/

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Rat.HeightOneSpectrum

open scoped IsDedekindDomain.FiniteAdeleRing

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The height-one prime of `ℤ` attached to a prime number `p`. -/
noncomputable def placeOfPrime (p : Nat.Primes) : HeightOneSpectrum ℤ :=
  (primesEquiv (R := ℤ)).symm p

/-- **The `p`-adic points inside the finite-adelic points**: the group homomorphism
`GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ]` identifying `ℚ_[p]` with the completion of `ℚ` at the place
`(p)`, then placing the matrix there and the identity matrix at every other place. -/
noncomputable def padicToFiniteAdeles (p : Nat.Primes) : GL n ℚ_[p] →* GL n 𝔸ᶠ[ℤ, ℚ] :=
  (localGL (placeOfPrime p)).comp
    (Matrix.GeneralLinearGroup.map
      (Padic.adicCompletionEquiv ℤ p).toAlgEquiv.toRingEquiv.toRingHom)

/-! ### The local action on automorphic forms -/

section LocalAction

/-- Right translation on the automorphic forms, restricted to `GL n ℚ_[p]` along
`padicToFiniteAdeles`: the representation of `GL n ℚ_[p]` through which the spherical Hecke
algebra at `p` acts on the global object. -/
noncomputable def localRepresentation (p : Nat.Primes) :
    Representation ℂ (GL n ℚ_[p]) (automorphicForms n) :=
  (rightTranslation n).comp (padicToFiniteAdeles p)

/-- An automorphic form is **unramified at `p`** when it is fixed by right translation by
(the image of) `GL n ℤ_[p]`. This is the condition under which the spherical Hecke operators
at `p` act on it. -/
def IsUnramifiedAt (p : Nat.Primes) (f : automorphicForms n) : Prop :=
  f ∈ (localRepresentation p).subgroupInvariants (integralSubgroup n ℤ_[p] ℚ_[p])

theorem isUnramifiedAt_iff {p : Nat.Primes} {f : automorphicForms n} :
    IsUnramifiedAt p f ↔ ∀ g ∈ integralSubgroup n ℤ_[p] ℚ_[p],
      rightTranslation n (padicToFiniteAdeles p g) f = f :=
  Representation.mem_subgroupInvariants

end LocalAction

/-! ### The Hecke operators `T_{p,i}` -/

section HeckeOperator

/-- `p` as a unit of `ℚ_[p]`: the uniformizer at which the spherical Hecke operators sit. -/
noncomputable def padicUnit (p : Nat.Primes) : ℚ_[p]ˣ :=
  Units.mk0 ((p : ℕ) : ℚ_[p]) (Nat.cast_ne_zero.mpr p.2.ne_zero)

@[simp]
theorem val_padicUnit (p : Nat.Primes) : (padicUnit p : ℚ_[p]) = ((p : ℕ) : ℚ_[p]) := rfl

variable {m : ℕ}

/-- **The spherical Hecke operator `T_{p,i}` on automorphic forms**: the Hecke operator at
the double coset of `diag (p, …, p, 1, …, 1)`, with `i` entries `p`, acting on the
`GL m ℤ_[p]`-invariant (i.e. unramified-at-`p`) automorphic forms. It exists with no further
hypotheses because `GL m ℤ_[p]` is a Hecke subgroup of `GL m ℚ_[p]`. -/
noncomputable def adelicHeckeT (p : Nat.Primes) (i : ℕ) :
    (localRepresentation (n := Fin m) p).subgroupInvariants
        (integralSubgroup (Fin m) ℤ_[p] ℚ_[p]) →ₗ[ℂ]
      (localRepresentation (n := Fin m) p).subgroupInvariants
        (integralSubgroup (Fin m) ℤ_[p] ℚ_[p]) :=
  T (localRepresentation p) (fun _ ha => PadicInt.finite_quotient_span_singleton ha)
    (padicUnit p) i

/-- `T_{p,0}` is the identity. -/
@[simp]
theorem adelicHeckeT_zero (p : Nat.Primes) :
    adelicHeckeT (m := m) p 0 = LinearMap.id :=
  T_zero _ _ _

end HeckeOperator

end Matrix.GeneralLinearGroup
