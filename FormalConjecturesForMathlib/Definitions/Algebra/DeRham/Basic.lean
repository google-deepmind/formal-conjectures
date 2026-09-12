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

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Algebraic de Rham forms

Relative differential forms of degree `p` are the exterior powers `⋀[A]^p Ω[A⁄R]` of the module
of relative Kähler differentials, built from Mathlib's `exteriorPower` and `KaehlerDifferential`.
Since `⋀[A]^p M` is a submodule of `ExteriorAlgebra A M`, all degrees live inside the single
algebra `ExtAlg R A = ⋀ Ω[A⁄R]`, and the exterior derivative is constructed once and for all on
that algebra.

## The exterior derivative

The exterior derivative is the odd degree-one `R`-derivation `d` of `⋀ Ω[A⁄R]` extending the
universal derivation `A → Ω[A⁄R]`. It is obtained from a universal property rather than from a
choice of generators: an odd derivation is the same thing as an algebra map `x ↦ x + (d x) * ε`
into the square-zero extension `Sq R A = ⋀ Ω[A⁄R] ⊕ ⋀ Ω[A⁄R] * ε` by an odd square-zero element,
whose multiplication `(x, u) * (y, v) = (x * y, involute x * v + u * y)` encodes the graded
Leibniz rule. Here `involute` is the grade involution, so `involute x = (-1) ^ p * x` on a form of
degree `p`, and the rule read off from that product is the usual
`d (x * y) = d x * y + (-1) ^ p * x * d y`.

Giving `Sq R A` the twisted `A`-algebra structure `a ↦ a + (d a) * ε` turns that algebra map into
an `A`-algebra map, so it is produced in two steps:

* the universal property of `Ω[A⁄R]` applied to the derivation `a ↦ (d a) * ε` gives an
  `A`-linear `phi : Ω[A⁄R] → Sq R A`, necessarily of the form `ω ↦ ω + (d ω) * ε`;
* the universal property of the exterior algebra applied to `phi` gives `deRhamHom`, and `d` is
  its `ε`-component `extDeriv`.

The identities `d ∘ d = 0`, the graded Leibniz rule, and the fact that `d` raises the degree by
one then follow by induction on the exterior algebra.

## Main definitions

* `Algebra.DeRham.Form R A p`: differential forms of degree `p`, that is `⋀[A]^p Ω[A⁄R]`;
* `Algebra.DeRham.differential`: the exterior derivative `Form R A p →ₗ[R] Form R A (p + 1)`;
* `Algebra.DeRham.mk R A p a₀ v`: the form `a₀ * d v₀ ∧ ... ∧ d vₚ₋₁`; these span `Form R A p`
  over `R`, by `Algebra.DeRham.span_mk`;
* `Algebra.DeRham.map`: functoriality along an `R`-algebra homomorphism.
-/

@[expose] public noncomputable section

universe u

namespace Algebra.DeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The exterior algebra of the module of relative Kähler differentials. Differential forms of
each degree live inside it as the exterior powers of `Ω[A⁄R]`. -/
abbrev ExtAlg : Type u := ExteriorAlgebra A Ω[A⁄R]

/-- The grade involution of `⋀ Ω[A⁄R]`, negating each differential. -/
abbrev involute : ExtAlg R A →ₐ[A] ExtAlg R A := CliffordAlgebra.involute

variable {R A}

@[simp] lemma involute_algebraMap (a : A) :
    involute R A (algebraMap A (ExtAlg R A) a) = algebraMap A (ExtAlg R A) a :=
  AlgHom.commutes _ a

@[simp] lemma involute_ι (ω : Ω[A⁄R]) :
    involute R A (ExteriorAlgebra.ι A ω) = -ExteriorAlgebra.ι A ω :=
  CliffordAlgebra.involute_ι ω

/-- A single differential anticommutes with every homogeneous factor, which globally reads as
commuting past the grade involution. -/
private lemma ι_mul_eq_involute_mul_ι (m : Ω[A⁄R]) (y : ExtAlg R A) :
    ExteriorAlgebra.ι A m * y = involute R A y * ExteriorAlgebra.ι A m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap a => rw [involute_algebraMap, Algebra.commutes]
  | ι n =>
      rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
      exact ExteriorAlgebra.ι_add_mul_swap m n
  | mul y z hy hz => rw [← mul_assoc, hy, mul_assoc, hz, ← mul_assoc, map_mul]
  | add y z hy hz => rw [mul_add, hy, hz, map_add, add_mul]

variable (R A)

/-- The square-zero extension of `⋀ Ω[A⁄R]` by an odd square-zero element `ε`, with elements
written `x + u * ε` and multiplication `(x, u) * (y, v) = (x * y, involute x * v + u * y)`.
An `R`-algebra map `x ↦ (x, d x)` into it is precisely an odd degree-one `R`-derivation `d`. -/
def Sq : Type u := ExtAlg R A × ExtAlg R A

namespace Sq

variable {R A}

/-- The element `x + u * ε` of the square-zero extension. -/
def mk (x u : ExtAlg R A) : Sq R A := (x, u)

/-- The part of an element of the square-zero extension not involving `ε`. -/
def fst (s : Sq R A) : ExtAlg R A := Prod.fst s

/-- The coefficient of `ε` in an element of the square-zero extension. -/
def snd (s : Sq R A) : ExtAlg R A := Prod.snd s

@[simp] lemma fst_mk (x u : ExtAlg R A) : fst (mk x u) = x := rfl

@[simp] lemma snd_mk (x u : ExtAlg R A) : snd (mk x u) = u := rfl

@[ext] lemma ext {s t : Sq R A} (h₁ : fst s = fst t) (h₂ : snd s = snd t) : s = t :=
  Prod.ext h₁ h₂

instance instAddCommGroup : AddCommGroup (Sq R A) :=
  inferInstanceAs (AddCommGroup (ExtAlg R A × ExtAlg R A))

@[simp] lemma fst_zero : fst (0 : Sq R A) = 0 := rfl

@[simp] lemma snd_zero : snd (0 : Sq R A) = 0 := rfl

@[simp] lemma fst_add (s t : Sq R A) : fst (s + t) = fst s + fst t := rfl

@[simp] lemma snd_add (s t : Sq R A) : snd (s + t) = snd s + snd t := rfl

@[simp] lemma fst_neg (s : Sq R A) : fst (-s) = -fst s := rfl

@[simp] lemma snd_neg (s : Sq R A) : snd (-s) = -snd s := rfl

instance : Mul (Sq R A) :=
  ⟨fun s t => mk (fst s * fst t) (involute R A (fst s) * snd t + snd s * fst t)⟩

@[simp] lemma fst_mul (s t : Sq R A) : fst (s * t) = fst s * fst t := rfl

@[simp] lemma snd_mul (s t : Sq R A) :
    snd (s * t) = involute R A (fst s) * snd t + snd s * fst t := rfl

instance : One (Sq R A) := ⟨mk 1 0⟩

@[simp] lemma fst_one : fst (1 : Sq R A) = 1 := rfl

@[simp] lemma snd_one : snd (1 : Sq R A) = 0 := rfl

instance instRing : Ring (Sq R A) where
  __ := instAddCommGroup (R := R) (A := A)
  mul_assoc s t u := by
    ext
    · simp [mul_assoc]
    · simp [map_mul, mul_add, add_mul, mul_assoc, add_assoc]
  one_mul s := by ext <;> simp
  mul_one s := by ext <;> simp
  left_distrib s t u := by
    ext
    · simp [mul_add]
    · simp only [fst_add, snd_add, snd_mul, mul_add]
      abel
  right_distrib s t u := by
    ext
    · simp [add_mul]
    · simp only [fst_add, snd_add, snd_mul, map_add, add_mul]
      abel
  zero_mul s := by ext <;> simp
  mul_zero s := by ext <;> simp

end Sq

/-- The twisted embedding `a ↦ a + (d a) * ε` of `A` into the square-zero extension. -/
def twist : A →+* Sq R A where
  toFun a := Sq.mk (algebraMap A (ExtAlg R A) a)
    (ExteriorAlgebra.ι A (KaehlerDifferential.D R A a))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Algebra.smul_def, Algebra.commutes (R := A) b (ExteriorAlgebra.ι A _)]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

@[simp] lemma fst_twist (a : A) :
    Sq.fst (twist R A a) = algebraMap A (ExtAlg R A) a := rfl

@[simp] lemma snd_twist (a : A) :
    Sq.snd (twist R A a) = ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) := rfl

lemma twist_commutes (a : A) (s : Sq R A) : twist R A a * s = s * twist R A a := by
  ext
  · simpa using Algebra.commutes a (Sq.fst s)
  · simp only [Sq.snd_mul, fst_twist, snd_twist, involute_algebraMap,
      ι_mul_eq_involute_mul_ι (KaehlerDifferential.D R A a) (Sq.fst s)]
    rw [Algebra.commutes a (Sq.snd s)]
    abel

instance : Algebra A (Sq R A) := (twist R A).toAlgebra' (twist_commutes R A)

instance : Algebra R (Sq R A) :=
  ((twist R A).comp (algebraMap R A)).toAlgebra' fun _ s => twist_commutes R A _ s

instance : IsScalarTower R A (Sq R A) := .of_algebraMap_eq fun _ => rfl

namespace Sq

variable {R A}

@[simp] lemma fst_algebraMap (a : A) :
    fst (algebraMap A (Sq R A) a) = algebraMap A (ExtAlg R A) a := rfl

@[simp] lemma snd_algebraMap (a : A) :
    snd (algebraMap A (Sq R A) a) = ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) := rfl

@[simp] lemma fst_smul (a : A) (s : Sq R A) : fst (a • s) = a • fst s := by
  rw [Algebra.smul_def, fst_mul, fst_algebraMap, Algebra.smul_def]

lemma snd_smul (a : A) (s : Sq R A) :
    snd (a • s) = a • snd s +
      ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * fst s := by
  rw [Algebra.smul_def, snd_mul, fst_algebraMap, snd_algebraMap, involute_algebraMap,
    Algebra.smul_def]

@[simp] lemma fst_smul_base (r : R) (s : Sq R A) : fst (r • s) = r • fst s := by
  rw [← algebraMap_smul A r s, fst_smul, algebraMap_smul]

@[simp] lemma snd_smul_base (r : R) (s : Sq R A) : snd (r • s) = r • snd s := by
  rw [← algebraMap_smul A r s, snd_smul, algebraMap_smul]
  simp

end Sq

namespace Sq

/-- The projection to the `ε`-free part, as an `A`-algebra map. -/
def fstAlgHom : Sq R A →ₐ[A] ExtAlg R A where
  toFun := fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma fstAlgHom_apply (s : Sq R A) : fstAlgHom R A s = fst s := rfl

/-- The coefficient of `ε`, as an `R`-linear map. -/
def sndLinear : Sq R A →ₗ[R] ExtAlg R A where
  toFun := snd
  map_add' _ _ := rfl
  map_smul' := snd_smul_base

@[simp] lemma sndLinear_apply (s : Sq R A) : sndLinear R A s = snd s := rfl

end Sq

/-- The tautological `R`-derivation `a ↦ (d a) * ε` of `A` into the square-zero extension. -/
def epsDerivation : Derivation R A (Sq R A) where
  toFun a := Sq.mk (ExteriorAlgebra.ι A (KaehlerDifferential.D R A a)) 0
  map_add' a b := by ext <;> simp
  map_smul' r a := by ext <;> simp
  map_one_eq_zero' := by ext <;> simp
  leibniz' a b := by
    ext
    · simp
    · simp [Sq.snd_smul, ExteriorAlgebra.ι_add_mul_swap]

/-- Every differential `ω` determines the element `ω + (d ω) * ε` of the square-zero extension.
This is the lift of `epsDerivation` along the universal property of Kähler differentials. -/
def phi : Ω[A⁄R] →ₗ[A] Sq R A := (epsDerivation R A).liftKaehlerDifferential

@[simp] lemma phi_D (a : A) :
    phi R A (KaehlerDifferential.D R A a) =
      Sq.mk (ExteriorAlgebra.ι A (KaehlerDifferential.D R A a)) 0 :=
  (epsDerivation R A).liftKaehlerDifferential_comp_D a

/-- To prove a statement about every Kähler differential it suffices to treat the exact ones
`d a` and to check closure under zero, sums, and scalars. -/
@[elab_as_elim]
lemma D_induction {motive : Ω[A⁄R] → Prop} (ω : Ω[A⁄R])
    (D : ∀ a : A, motive (KaehlerDifferential.D R A a)) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (a : A) x, motive x → motive (a • x)) : motive ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ hx => obtain ⟨a, rfl⟩ := hx; exact D a
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul a x _ hx => exact smul a x hx

@[simp] lemma fst_phi (ω : Ω[A⁄R]) : Sq.fst (phi R A ω) = ExteriorAlgebra.ι A ω := by
  have h : (Sq.fstAlgHom R A).toLinearMap.comp (phi R A) = ExteriorAlgebra.ι A := by
    refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A) ?_
    rintro _ ⟨a, rfl⟩
    simp
  exact congrArg (fun f => f ω) h

lemma snd_phi_smul (a : A) (ω : Ω[A⁄R]) :
    Sq.snd (phi R A (a • ω)) =
      a • Sq.snd (phi R A ω) +
        ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * ExteriorAlgebra.ι A ω := by
  rw [map_smul, Sq.snd_smul, fst_phi]

/-- The exterior derivative of a differential is an even element, so it commutes with everything
of degree one. -/
lemma involute_snd_phi (ω : Ω[A⁄R]) :
    involute R A (Sq.snd (phi R A ω)) = Sq.snd (phi R A ω) := by
  induction ω using D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a x hx =>
      rw [snd_phi_smul, map_add, map_smul, hx, map_mul, involute_ι, involute_ι, neg_mul_neg]

lemma phi_mul_self (ω : Ω[A⁄R]) : phi R A ω * phi R A ω = 0 := by
  ext
  · simp
  · rw [Sq.snd_mul, fst_phi, involute_ι, neg_mul, Sq.snd_zero,
      ι_mul_eq_involute_mul_ι, involute_snd_phi, neg_add_cancel]

/-- The exterior derivative on `⋀ Ω[A⁄R]`, packaged as the algebra map `x ↦ x + (d x) * ε` into
the square-zero extension. -/
def deRhamHom : ExtAlg R A →ₐ[A] Sq R A :=
  ExteriorAlgebra.lift A ⟨phi R A, phi_mul_self R A⟩

@[simp] lemma deRhamHom_ι (ω : Ω[A⁄R]) :
    deRhamHom R A (ExteriorAlgebra.ι A ω) = phi R A ω :=
  ExteriorAlgebra.lift_ι_apply A _ _ ω

@[simp] lemma fst_deRhamHom (x : ExtAlg R A) : Sq.fst (deRhamHom R A x) = x := by
  have h : (Sq.fstAlgHom R A).comp (deRhamHom R A) = AlgHom.id A (ExtAlg R A) := by
    apply ExteriorAlgebra.hom_ext
    ext ω
    simp
  exact AlgHom.congr_fun h x

/-- The exterior derivative on the exterior algebra of Kähler differentials. -/
def extDeriv : ExtAlg R A →ₗ[R] ExtAlg R A :=
  (Sq.sndLinear R A).comp ((deRhamHom R A).toLinearMap.restrictScalars R)

@[simp] lemma extDeriv_ι (ω : Ω[A⁄R]) :
    extDeriv R A (ExteriorAlgebra.ι A ω) = Sq.snd (phi R A ω) := by
  simp [extDeriv]

@[simp] lemma extDeriv_algebraMap (a : A) :
    extDeriv R A (algebraMap A (ExtAlg R A) a) =
      ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) := by
  show Sq.snd (deRhamHom R A (algebraMap A (ExtAlg R A) a)) = _
  rw [AlgHom.commutes]
  rfl

/-- The exterior derivative is an odd derivation of the exterior algebra. -/
lemma extDeriv_mul (x y : ExtAlg R A) :
    extDeriv R A (x * y) =
      involute R A x * extDeriv R A y + extDeriv R A x * y := by
  show Sq.snd (deRhamHom R A (x * y)) = _
  simp only [map_mul, Sq.snd_mul, fst_deRhamHom]
  rfl

/-- Multiplying forms adds their degrees. -/
private lemma mul_mem_exteriorPower {m n : ℕ} {x y : ExtAlg R A}
    (hx : x ∈ ⋀[A]^m Ω[A⁄R]) (hy : y ∈ ⋀[A]^n Ω[A⁄R]) :
    x * y ∈ ⋀[A]^(m + n) Ω[A⁄R] := by
  rw [ExteriorAlgebra.exteriorPower, pow_add]
  exact Submodule.mul_mem_mul hx hy

private lemma ι_mem_exteriorPower (ω : Ω[A⁄R]) :
    ExteriorAlgebra.ι A ω ∈ ⋀[A]^1 Ω[A⁄R] := by
  rw [ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ _

private lemma snd_phi_mem (ω : Ω[A⁄R]) : Sq.snd (phi R A ω) ∈ ⋀[A]^2 Ω[A⁄R] := by
  induction ω using D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => rw [map_add, Sq.snd_add]; exact Submodule.add_mem _ hx hy
  | smul a x hx =>
      rw [snd_phi_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx)
        (mul_mem_exteriorPower R A (ι_mem_exteriorPower R A _) (ι_mem_exteriorPower R A _))

/-- The exterior derivative raises the degree of a form by one. -/
lemma extDeriv_mem (p : ℕ) {x : ExtAlg R A} (hx : x ∈ ⋀[A]^p Ω[A⁄R]) :
    extDeriv R A x ∈ ⋀[A]^(p + 1) Ω[A⁄R] := by
  induction p generalizing x with
  | zero =>
      rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_range] at hx
      obtain ⟨a, rfl⟩ := hx
      simp
  | succ p ih =>
      rw [ExteriorAlgebra.exteriorPower, pow_succ'] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · rintro m hm n hn
        obtain ⟨ω, rfl⟩ := hm
        rw [extDeriv_mul, involute_ι, extDeriv_ι]
        refine Submodule.add_mem _ ?_ ?_
        · rw [neg_mul]
          have := mul_mem_exteriorPower R A (ι_mem_exteriorPower R A ω) (ih hn)
          rw [show 1 + (p + 1) = p + 1 + 1 by omega] at this
          exact Submodule.neg_mem _ this
        · have := mul_mem_exteriorPower R A (snd_phi_mem R A ω) hn
          rwa [show 2 + p = p + 1 + 1 by omega] at this
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy

/-! ### Differential forms -/

/-- Relative Kähler differential forms of degree `p`: the `p`-th exterior power over `A` of the
module of relative Kähler differentials `Ω[A⁄R]`. -/
abbrev Form (p : ℕ) : Type u := ↥(⋀[A]^p Ω[A⁄R])

/-- The exterior derivative on differential forms of degree `p`. -/
def differential (p : ℕ) : Form R A p →ₗ[R] Form R A (p + 1) where
  toFun x := ⟨extDeriv R A x, extDeriv_mem R A p x.2⟩
  map_add' _ _ := Subtype.ext (map_add (extDeriv R A) _ _)
  map_smul' r _ := Subtype.ext (map_smul (extDeriv R A) r _)

@[simp] lemma coe_differential (p : ℕ) (x : Form R A p) :
    (differential R A p x : ExtAlg R A) = extDeriv R A x := rfl

private lemma extDeriv_smul (a : A) (x : ExtAlg R A) :
    extDeriv R A (a • x) =
      a • extDeriv R A x +
        ExteriorAlgebra.ι A (KaehlerDifferential.D R A a) * x := by
  rw [Algebra.smul_def, extDeriv_mul, involute_algebraMap, extDeriv_algebraMap,
    ← Algebra.smul_def]

/-- The exact form `d a₁ ∧ ⋯ ∧ d aₚ`. -/
def exact (p : ℕ) (v : Fin p → A) : Form R A p :=
  exteriorPower.ιMulti A p fun i => KaehlerDifferential.D R A (v i)

@[simp] lemma coe_exact (p : ℕ) (v : Fin p → A) :
    (exact R A p v : ExtAlg R A) =
      ExteriorAlgebra.ιMulti A p fun i => KaehlerDifferential.D R A (v i) := rfl

/-- Wedges of exact forms are closed. -/
private lemma extDeriv_exact (p : ℕ) (v : Fin p → A) :
    extDeriv R A (exact R A p v : ExtAlg R A) = 0 := by
  induction p with
  | zero =>
      rw [coe_exact, ExteriorAlgebra.ιMulti_zero_apply,
        ← map_one (algebraMap A (ExtAlg R A)), extDeriv_algebraMap]
      simp
  | succ p ih =>
      rw [coe_exact, ExteriorAlgebra.ιMulti_succ_apply, extDeriv_mul, involute_ι,
        extDeriv_ι, phi_D, Sq.snd_mk, zero_mul, add_zero]
      have : (Matrix.vecTail fun i => KaehlerDifferential.D R A (v i)) =
          fun i => KaehlerDifferential.D R A (Matrix.vecTail v i) := rfl
      rw [this, ← coe_exact R A p (Matrix.vecTail v), ih (Matrix.vecTail v), mul_zero]

/-- The differential form `a₀ * d a₁ ∧ ⋯ ∧ d aₚ`. Such forms span the degree `p` forms over the
base ring. -/
def mk (p : ℕ) (a₀ : A) (v : Fin p → A) : Form R A p := a₀ • exact R A p v

@[simp] lemma coe_mk (p : ℕ) (a₀ : A) (v : Fin p → A) :
    (mk R A p a₀ v : ExtAlg R A) =
      a₀ • ExteriorAlgebra.ιMulti A p fun i => KaehlerDifferential.D R A (v i) := rfl

@[simp] lemma differential_mk (p : ℕ) (a₀ : A) (v : Fin p → A) :
    differential R A p (mk R A p a₀ v) = mk R A (p + 1) 1 (Fin.cons a₀ v) := by
  refine Subtype.ext ?_
  rw [coe_differential, coe_mk, coe_mk, extDeriv_smul, ← coe_exact, extDeriv_exact,
    smul_zero, zero_add, one_smul, ExteriorAlgebra.ιMulti_succ_apply]
  rfl

/-- A function regarded as a differential form of degree zero. -/
def ofFunction : A →ₗ[R] Form R A 0 where
  toFun a := mk R A 0 a Fin.elim0
  map_add' a b := by simp [mk, add_smul]
  map_smul' r a := by simp [mk, smul_assoc]

lemma ofFunction_apply (a : A) : ofFunction R A a = mk R A 0 a Fin.elim0 := rfl

/-- A scalar from the base ring regarded as a differential form of degree zero. -/
def ofConstant : R →ₗ[R] Form R A 0 :=
  (ofFunction R A).comp (Algebra.linearMap R A)

lemma ofConstant_apply (r : R) :
    ofConstant R A r = ofFunction R A (algebraMap R A r) := rfl

@[simp] lemma differential_ofFunction_algebraMap (r : R) :
    differential R A 0 (ofFunction R A (algebraMap R A r)) = 0 := by
  refine Subtype.ext ?_
  rw [ofFunction_apply, coe_differential, coe_mk, extDeriv_smul, ← coe_exact,
    extDeriv_exact, smul_zero, zero_add]
  simp

@[simp] lemma differential_ofConstant (r : R) :
    differential R A 0 (ofConstant R A r) = 0 := by
  rw [ofConstant_apply, differential_ofFunction_algebraMap]

/-! ### Generators -/

/-- Exact forms span the differential forms of degree `p` over `A`. -/
private lemma span_exact (p : ℕ) :
    Submodule.span A (Set.range fun v : Fin p → A => exact R A p v) = ⊤ := by
  rw [← top_le_iff, ← exteriorPower.ιMulti_span_of_span A p Ω[A⁄R]
    (KaehlerDifferential.span_range_derivation R A), Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  choose v hv using fun i => hw ⟨i, rfl⟩
  exact Submodule.subset_span ⟨v, congrArg _ (funext hv)⟩

/-- Forms `a₀ * d a₁ ∧ ⋯ ∧ d aₚ` span the differential forms of degree `p` over the base ring. -/
private lemma span_mk (p : ℕ) :
    Submodule.span R (Set.range fun av : A × (Fin p → A) => mk R A p av.1 av.2) = ⊤ := by
  have key : ∀ x : Form R A p,
      x ∈ Submodule.span A (Set.range fun v : Fin p → A => exact R A p v) → ∀ a : A,
      a • x ∈ Submodule.span R (Set.range fun av : A × (Fin p → A) => mk R A p av.1 av.2) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨v, rfl⟩ := hy; exact fun a => Submodule.subset_span ⟨(a, v), rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
        exact fun a => by rw [smul_add]; exact Submodule.add_mem _ (hy a) (hz a)
    | smul b y _ hy => exact fun a => by rw [smul_smul]; exact hy _
  exact top_unique fun x _ => by simpa using key x (by rw [span_exact]; trivial) 1

/-- Two `R`-linear maps out of degree `p` forms agreeing on the generators are equal. -/
private lemma linearMap_ext {M : Type*} [AddCommGroup M] [Module R M] {p : ℕ}
    {F G : Form R A p →ₗ[R] M} (h : ∀ a₀ v, F (mk R A p a₀ v) = G (mk R A p a₀ v)) : F = G :=
  LinearMap.ext_on (span_mk R A p) (by rintro _ ⟨⟨a₀, v⟩, rfl⟩; exact h a₀ v)

@[simp] lemma mk_smul_coeff (p : ℕ) (r : R) (a₀ : A) (v : Fin p → A) :
    mk R A p (r • a₀) v = r • mk R A p a₀ v :=
  smul_assoc r a₀ _

@[simp] lemma mk_zero_coeff (p : ℕ) (v : Fin p → A) : mk R A p 0 v = 0 :=
  zero_smul A _

/-- To prove a statement about every differential form of degree `p` it suffices to treat the
generators `a₀ * d v₀ ∧ ... ∧ d vₚ₋₁` and to check closure under zero, sums, and scalars. -/
@[elab_as_elim]
lemma mk_induction {p : ℕ} {motive : Form R A p → Prop} (x : Form R A p)
    (mk : ∀ (a₀ : A) (v : Fin p → A), motive (_root_.Algebra.DeRham.mk R A p a₀ v))
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (r : R) x, motive x → motive (r • x)) : motive x := by
  have hx : x ∈ Submodule.span R
      (Set.range fun av : A × (Fin p → A) => _root_.Algebra.DeRham.mk R A p av.1 av.2) := by
    rw [span_mk]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨⟨a₀, v⟩, rfl⟩ := hy; exact mk a₀ v
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul r y _ hy => exact smul r y hy

/-! ### Functoriality -/

section Tower

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The algebra map on exterior algebras of Kähler differentials attached to a tower
`R → A → B`. -/
def extAlgMap : ExtAlg R A →ₐ[A] ExtAlg R B :=
  ExteriorAlgebra.lift A
    ⟨((ExteriorAlgebra.ι B).restrictScalars A).comp (KaehlerDifferential.map R R A B),
      fun _ => ExteriorAlgebra.ι_sq_zero _⟩

@[simp] lemma extAlgMap_ι (ω : Ω[A⁄R]) :
    extAlgMap R A B (ExteriorAlgebra.ι A ω) =
      ExteriorAlgebra.ι B (KaehlerDifferential.map R R A B ω) :=
  ExteriorAlgebra.lift_ι_apply A _ _ ω

@[simp] lemma extAlgMap_algebraMap (a : A) :
    extAlgMap R A B (algebraMap A (ExtAlg R A) a) =
      algebraMap B (ExtAlg R B) (algebraMap A B a) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B (ExtAlg R B)]

@[simp] lemma extAlgMap_algebraMap_base (r : R) :
    extAlgMap R A B (algebraMap R (ExtAlg R A) r) = algebraMap R (ExtAlg R B) r := by
  rw [IsScalarTower.algebraMap_apply R A (ExtAlg R A), extAlgMap_algebraMap,
    ← IsScalarTower.algebraMap_apply R A B, ← IsScalarTower.algebraMap_apply R B (ExtAlg R B)]

private lemma extAlgMap_ιMulti (p : ℕ) (w : Fin p → Ω[A⁄R]) :
    extAlgMap R A B (ExteriorAlgebra.ιMulti A p w) =
      ExteriorAlgebra.ιMulti B p fun i => KaehlerDifferential.map R R A B (w i) := by
  induction p with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ p ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, extAlgMap_ι,
        ExteriorAlgebra.ιMulti_succ_apply, ih (Matrix.vecTail w)]
      rfl

lemma extAlgMap_mem (p : ℕ) {x : ExtAlg R A} (hx : x ∈ ⋀[A]^p Ω[A⁄R]) :
    extAlgMap R A B x ∈ ⋀[B]^p Ω[B⁄R] := by
  induction p generalizing x with
  | zero =>
      rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_range] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_range]
      exact ⟨algebraMap A B a, (extAlgMap_algebraMap R A B a).symm⟩
  | succ p ih =>
      rw [ExteriorAlgebra.exteriorPower, pow_succ'] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · rintro _ ⟨ω, rfl⟩ n hn
        rw [map_mul, extAlgMap_ι]
        have := mul_mem_exteriorPower R B
          (ι_mem_exteriorPower R B (KaehlerDifferential.map R R A B ω)) (ih hn)
        rwa [show 1 + p = p + 1 by omega] at this
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy

/-- Pull differential forms forward along a tower `R → A → B`. -/
def mapTower (p : ℕ) : Form R A p →ₗ[R] Form R B p where
  toFun x := ⟨extAlgMap R A B x, extAlgMap_mem R A B p x.2⟩
  map_add' x y := Subtype.ext (map_add (extAlgMap R A B) _ _)
  map_smul' r x := Subtype.ext (by
    show extAlgMap R A B (r • (x : ExtAlg R A)) = r • extAlgMap R A B (x : ExtAlg R A)
    rw [Algebra.smul_def, map_mul, extAlgMap_algebraMap_base, Algebra.smul_def])

@[simp] lemma coe_mapTower (p : ℕ) (x : Form R A p) :
    (mapTower R A B p x : ExtAlg R B) = extAlgMap R A B x := rfl

end Tower

section AlgHomMap

variable {A}
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- Pull differential forms forward along an algebra homomorphism. -/
def map (f : A →ₐ[R] B) (p : ℕ) : Form R A p →ₗ[R] Form R B p :=
  letI := f.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  mapTower R A B p

@[simp] lemma map_mk (f : A →ₐ[R] B) (p : ℕ) (a₀ : A) (v : Fin p → A) :
    map R f p (mk R A p a₀ v) = mk R B p (f a₀) fun i => f (v i) := by
  let _ := f.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  refine Subtype.ext ?_
  show extAlgMap R A B (mk R A p a₀ v : ExtAlg R A) =
    ((mk R B p (f a₀) fun i => f (v i) : Form R B p) : ExtAlg R B)
  rw [coe_mk, coe_mk, map_smul, extAlgMap_ιMulti]
  have hfam : (fun i => KaehlerDifferential.map R R A B (KaehlerDifferential.D R A (v i))) =
      fun i => KaehlerDifferential.D R B (f (v i)) := by
    funext i
    exact KaehlerDifferential.map_D R R A B (v i)
  rw [hfam]
  exact (algebraMap_smul (R := A) B a₀ _).symm

@[simp] lemma map_id (p : ℕ) : map R (AlgHom.id R A) p = LinearMap.id :=
  linearMap_ext R A fun a₀ v => by simp

@[simp] lemma map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (p : ℕ) :
    map R (g.comp f) p = (map R g p).comp (map R f p) :=
  linearMap_ext R A fun a₀ v => by simp

@[simp] lemma map_ofFunction (f : A →ₐ[R] B) (a : A) :
    map R f 0 (ofFunction R A a) = ofFunction R B (f a) := by
  rw [ofFunction_apply, map_mk, ofFunction_apply]
  congr 1
  exact funext fun i : Fin 0 => i.elim0

@[simp] lemma map_ofConstant (f : A →ₐ[R] B) (r : R) :
    map R f 0 (ofConstant R A r) = ofConstant R B r := by
  rw [ofConstant_apply, map_ofFunction, f.commutes, ofConstant_apply]

end AlgHomMap

end Algebra.DeRham
