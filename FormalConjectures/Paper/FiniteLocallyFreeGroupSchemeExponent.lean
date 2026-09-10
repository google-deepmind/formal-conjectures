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

import FormalConjecturesUtil

/-!
# Is a finite locally free group scheme killed by its order?

A finite locally free group scheme of rank `n` is the group scheme analogue of a finite group of
order `n`. Lagrange's theorem gives `g ^ n = 1` in a finite group of order `n`, and Grothendieck
asked whether the `n`-th power map of such a group scheme is trivial. The answer is affirmative
over a reduced base and for commutative group schemes, and negative in general. Which exponent
does kill every group scheme of a given rank is open.

A group scheme is represented here by its coordinate Hopf algebra `A` over the base ring `R`.
`A` is not assumed to be cocommutative, so the group scheme is not assumed to be commutative.
The base is a ring rather than a scheme: a finite locally free group scheme is affine over its
base, and being killed by `m` is local on the base, so nothing is lost.

*References:*
- [M. Demazure and A. Grothendieck, *Schémas en groupes* (SGA 3), re-edition by P. Gille and
  P. Polo](https://webusers.imj-prg.fr/~patrick.polo/SGA3/). Exp. VIII, Rem. 7.3.1 poses the
  question; an editors' note records that the re-edition drops the commutativity assumption there.
  Exp. VIIA, Prop. 8.5 settles the case of a field and Cor. 8.5.2 the case of a reduced base.
- [R. Schoof, *Is a finite locally free group scheme killed by its
  order?*](https://reneschoof.github.io/schoof_oortAAG.pdf), a survey of the question and of the
  cases that are known, written before the counterexample
- [J. Tate and F. Oort, *Group schemes of prime order*](https://www.numdam.org/item/ASENS_1970_4_3_1_1_0/),
  p. 4 for Deligne's theorem and p. 5, which records the general question as open in 1970
- [Mathlib, *A finite free group scheme of rank four that is not killed by
  four*](https://leanprover-community.github.io/mathlib4_docs/Counterexamples/GrothendieckPower.html),
  the counterexample
-/

namespace FiniteLocallyFreeGroupSchemeExponent

open MonoidAlgebra WithConv

universe u v

/-- The group scheme `Spec A` of a commutative Hopf algebra `A` over `R` is killed by `m` when
the `m`-th convolution power of `AlgHom.id R A` is the convolution unit.

The convolution power of `AlgHom.id R A` is the coordinate map of the pointwise power map
`x ↦ x ^ m`, and `1` is the constant map at the identity section. -/
def IsKilledBy (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A]
    (m : ℕ) : Prop :=
  toConv (AlgHom.id R A) ^ m = 1

/-- A positive integer `m` is a universal killing exponent in rank `n` if every finite locally
free group scheme of rank `n`, over every commutative ring, is killed by `m`.

The hypotheses that `A` is finite and flat over `R`, with constant `rankAtStalk` equal to `n`,
express that the group scheme is finite locally free of rank `n`. -/
def IsUniversalKillingExponent (n m : ℕ+) : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Flat R A],
    Module.rankAtStalk (R := R) A = (fun _ ↦ (n : ℕ)) → IsKilledBy R A m

/-- Unfolding `IsKilledBy` at `m = 1`: the group scheme is trivial exactly when the identity of
`A` is the composite of the counit with the unit. -/
@[category API, AMS 14 16]
theorem isKilledBy_one_iff (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A] :
    IsKilledBy R A 1 ↔ AlgHom.id R A = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  rw [IsKilledBy, pow_one, AlgHom.convOne_def]
  exact ⟨fun h ↦ WithConv.toConv_injective h, fun h ↦ congrArg _ h⟩

/-- On a group algebra the `m`-th convolution power of the identity is the pointwise `m`-th power:
it sends the group-like element `single g 1` to `single (g ^ m) 1`. -/
@[category API, AMS 14 16]
theorem pow_apply_single (R : Type u) [CommRing R] (G : Type v) [CommGroup G] (m : ℕ) (g : G) :
    (toConv (AlgHom.id R (MonoidAlgebra R G)) ^ m).ofConv (single g 1) = single (g ^ m) 1 := by
  induction m with
  | zero =>
    simp [AlgHom.convOne_def, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one,
      MonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, AlgHom.convMul_apply, MonoidAlgebra.comul_single]
    simp [Coalgebra.comul, ih, single_mul_single, pow_succ]

/-- Every group scheme is killed by the exponent `0`, which is why the exponents in
`IsUniversalKillingExponent` are positive. -/
@[category test, AMS 14 16]
theorem isKilledBy_zero (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A] :
    IsKilledBy R A 0 :=
  pow_zero _

/-- `IsKilledBy` is not vacuous: the group scheme `μ₂ = Spec ℚ[ℤ/2]` is not killed by `1`. -/
@[category test, AMS 14 16]
theorem not_isKilledBy_one :
    ¬ IsKilledBy ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod 2))) 1 := by
  rw [isKilledBy_one_iff]
  intro h
  have h2 := DFunLike.congr_fun h (single (Multiplicative.ofAdd 1) (1 : ℚ))
  simp [MonoidAlgebra.single_left_inj (one_ne_zero (α := ℚ))] at h2

/-- `IsKilledBy` is not always false either: the diagonalisable group scheme `μₙ = Spec R[ℤ/n]`
is killed by `n`, in accordance with Deligne's theorem. -/
@[category test, AMS 14 16]
theorem isKilledBy_monoidAlgebra (R : Type u) [CommRing R] (n : ℕ) [NeZero n] :
    IsKilledBy R (MonoidAlgebra R (Multiplicative (ZMod n))) n := by
  refine WithConv.ext (MonoidAlgebra.algHom_ext (fun g ↦ ?_) (by ext))
  have hg : g ^ n = 1 := by
    have := pow_card_eq_one (G := Multiplicative (ZMod n)) (x := g)
    simpa [ZMod.card] using this
  show (toConv (AlgHom.id R (MonoidAlgebra R (Multiplicative (ZMod n)))) ^ n).ofConv
      (single g 1) = _
  rw [pow_apply_single, hg]
  simp [AlgHom.convOne_def, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one,
    MonoidAlgebra.one_def]

/-- The group scheme `μₙ = Spec R[ℤ/n]` has rank `n`. -/
@[category test, AMS 14 16]
theorem rankAtStalk_monoidAlgebra (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n] :
    Module.rankAtStalk (R := R) (MonoidAlgebra R (Multiplicative (ZMod n))) = fun _ ↦ n := by
  ext p
  rw [Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative (ZMod n)) R)]
  simp

/-- The hypotheses of `IsUniversalKillingExponent` are satisfiable in every rank `n`: they apply
to `μₙ = Spec R[ℤ/n]` over any nontrivial ring. -/
@[category test, AMS 14 16]
theorem isKilledBy_of_isUniversalKillingExponent (n m : ℕ+)
    (h : IsUniversalKillingExponent.{u, u} n m) (R : Type u) [CommRing R] [Nontrivial R] :
    IsKilledBy R (MonoidAlgebra R (Multiplicative (ZMod (n : ℕ)))) (m : ℕ) :=
  haveI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  h R _ (rankAtStalk_monoidAlgebra R n)

/--
Grothendieck's question: is every finite locally free group scheme of rank $n$, over every
commutative ring, killed by $n$?

The answer is no. There is a commutative Hopf algebra of rank $4$ over a finite non-reduced ring
whose fourth power map is not trivial; its eighth power map is trivial.
-/
@[category research solved, AMS 14 16, formal_proof using lean4 at
  "https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Counterexamples/GrothendieckPower.lean#L882-L892"]
theorem killed_by_rank :
    answer(False) ↔ ∀ n : ℕ+, IsUniversalKillingExponent.{u, v} n n := by
  sorry

/--
Over a field the answer is affirmative: a finite group scheme of rank $n$ over a field is killed
by $n$. This is [SGA 3], Exp. VIIA, Prop. 8.5.
-/
@[category research solved, AMS 14 16]
theorem killed_by_rank.variants.field (n : ℕ+) (k : Type*) [Field k] (A : Type*) [CommRing A]
    [HopfAlgebra k A] [Module.Finite k A] (hn : Module.finrank k A = (n : ℕ)) :
    IsKilledBy k A n := by
  sorry

/--
Over a reduced base ring the answer is affirmative: every finite locally free group scheme of
rank $n$ over a reduced commutative ring is killed by $n$. This is [SGA 3], Exp. VIIA, Cor. 8.5.2,
deduced there from the case of a field.
-/
@[category research solved, AMS 14 16]
theorem killed_by_rank.variants.reduced_base (n : ℕ+) (R : Type*) [CommRing R] [IsReduced R]
    (A : Type*) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Flat R A]
    (hn : Module.rankAtStalk (R := R) A = fun _ ↦ (n : ℕ)) :
    IsKilledBy R A n := by
  sorry

/--
Deligne's theorem: a finite locally free *commutative* group scheme of rank $n$ over any
commutative ring is killed by $n$. Commutativity of the group scheme is cocommutativity of its
coordinate Hopf algebra. See [SGA 3], Exp. VIIA, Rem. 8.5.3 and [TO70], p. 4.
-/
@[category research solved, AMS 14 16]
theorem killed_by_rank.variants.commutative (n : ℕ+) (R : Type*) [CommRing R] (A : Type*)
    [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Flat R A]
    (hn : Module.rankAtStalk (R := R) A = fun _ ↦ (n : ℕ)) :
    IsKilledBy R A n := by
  sorry

/--
Determine the function assigning to each positive integer $n$ the least positive integer $m$
such that every finite locally free group scheme of rank $n$, over every commutative ring, is
killed by $m$.

Grothendieck asked whether this least exponent is $n$ itself. It is not, already for $n = 4$.
The exponents that kill every group scheme of rank $n$ are the multiples of the least one, so
minimality for $\le$ agrees with minimality for divisibility.
-/
@[category research open, AMS 14 16]
theorem optimal_exponent :
    let exponent : ℕ+ → ℕ+ := answer(sorry)
    ∀ n, IsLeast {m | IsUniversalKillingExponent.{u, v} n m} (exponent n) := by
  sorry

end FiniteLocallyFreeGroupSchemeExponent
