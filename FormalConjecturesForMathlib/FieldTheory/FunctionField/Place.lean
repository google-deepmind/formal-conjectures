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

public import Mathlib.FieldTheory.RatFunc.Valuation

/-!
# Places of a field extension

This file defines the places of a field extension `F / K`, presented by their normalised
valuations, together with their valuation rings, residue fields and degrees. If `F / K` is the
function field of a curve, then the places are the closed points of the curve and the places of
degree one are its `K`-rational points.

The valuations follow Mathlib's multiplicative convention for adic valuations:
$v_P = \exp(-\operatorname{ord}_P)$, so that $\mathcal{O}_P = \{f \mid v_P(f) \leq 1\}$ and a
pole makes the valuation large.

The main example is `FunctionField.Place.atInfty`, the place at infinity of the projective line.
Its function field is `K(t)`, and the place has degree one (`FunctionField.Place.degree_atInfty`).

## References

- Henning Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer GTM 254,
  Section 1.1, https://doi.org/10.1007/978-3-540-76878-4
-/

@[expose] public section

namespace FunctionField

open Module (finrank)
open scoped WithZero
open WithZero (exp)

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A place of the field extension $F / K$, presented by its normalised valuation: a surjective
valuation `v : F → ℤᵐ⁰` that is trivial on `K`. Surjectivity is the usual normalisation
$v(F^\times) = \mathbb{Z}$; it also forces $v$ to be non-trivial. Every place of $F / K$ has
exactly one normalised valuation, and a valuation is recovered from its valuation ring, so this
is a faithful description of the set of places. -/
structure Place where
  /-- The normalised valuation of the place. -/
  v : Valuation F ℤᵐ⁰
  /-- The valuation is normalised: its value group is all of `ℤ`. -/
  surjective : Function.Surjective v
  /-- The valuation is trivial on `K`. -/
  isTrivialOn : v.IsTrivialOn K

attribute [instance] Place.isTrivialOn

namespace Place

variable {K F}

/-- A place is determined by its normalised valuation. -/
@[ext]
theorem ext {P Q : Place K F} (h : P.v = Q.v) : P = Q := by
  cases P; cases Q; subst h; rfl

/-- The valuation ring $\mathcal{O}_P = \{f \in F \mid v_P(f) \leq 1\}$ of a place `P`. -/
def integers (P : Place K F) : ValuationSubring F := P.v.valuationSubring

/-- Membership in the valuation ring of a place, unfolded. -/
theorem mem_integers {P : Place K F} {f : F} : f ∈ P.integers ↔ P.v f ≤ 1 := Iff.rfl

/-- A place is a non-trivial valuation, so its valuation ring is a proper subring of `F`. -/
theorem integers_ne_top (P : Place K F) : P.integers ≠ ⊤ := by
  obtain ⟨f, hf⟩ := P.surjective (exp 1)
  intro h
  have hmem : P.v f ≤ 1 := mem_integers.1 (h ▸ ValuationSubring.mem_top f)
  rw [hf, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
  norm_num at hmem

/-- The structure map from `K` to the valuation ring of a place of `F / K`. -/
def toIntegers (P : Place K F) : K →+* P.integers :=
  (algebraMap K F).codRestrict _ fun a => Valuation.IsTrivialOn.valuation_algebraMap_le_one P.v a

instance (P : Place K F) : Algebra K P.integers := P.toIntegers.toAlgebra

/-- The residue field $\mathcal{O}_P / \mathfrak{m}_P$ of a place. It is a `K`-vector space
through `Place.toIntegers`. -/
abbrev residueField (P : Place K F) : Type _ := IsLocalRing.ResidueField P.integers

/-- The degree $\deg P = [\mathcal{O}_P / \mathfrak{m}_P : K]$ of a place. It is finite and
positive for every place of a function field of one variable. -/
noncomputable def degree (P : Place K F) : ℕ := finrank K P.residueField

/-- A place has degree one exactly when its residue field is `K`, that is, when it is a
`K`-rational point of the curve. -/
theorem degree_eq_one_iff {P : Place K F} :
    P.degree = 1 ↔ Function.Bijective (algebraMap K P.residueField) :=
  Algebra.finrank_eq_one_iff_bijective_algebraMap

/-- A place has degree one if every element of its valuation ring is congruent to a constant
modulo the maximal ideal. -/
theorem degree_eq_one_of_forall_exists {P : Place K F}
    (h : ∀ f : F, P.v f ≤ 1 → ∃ c : K, P.v (f - algebraMap K F c) < 1) : P.degree = 1 := by
  refine degree_eq_one_iff.2 ⟨(algebraMap K P.residueField).injective, fun y => ?_⟩
  obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := h f f.2
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply K P.integers P.residueField,
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := P.v)).2 ?_
  change P.v (algebraMap K F c - f) < 1
  rwa [Valuation.map_sub_swap]

/-- The place at infinity of the projective line over `K`, whose function field is `K(t)`. It is
given by `v(f) = exp (deg (num f) - deg (denom f))`, so that `t`, which has a pole at infinity,
has valuation `exp 1 > 1`. -/
noncomputable def atInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    Place K (RatFunc K) where
  v := RatFunc.inftyValuation K
  surjective y := by
    induction y using WithZero.recZeroCoe with
    | zero => exact ⟨0, by simp [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]⟩
    | coe m =>
      refine ⟨RatFunc.X ^ (Multiplicative.toAdd m), ?_⟩
      rw [RatFunc.inftyValuation_apply, ← RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation.X_zpow]
      rfl
  isTrivialOn := inferInstance

variable (K) [DecidableEq (RatFunc K)]

/-- The valuation of the place at infinity is Mathlib's `RatFunc.inftyValuation`. -/
theorem atInfty_v : (atInfty K).v = RatFunc.inftyValuation K := rfl

/-- `t` has a pole at infinity, so it does not lie in the valuation ring of the place at
infinity. Together with `inv_X_mem_integers_atInfty` this pins down the direction of the
multiplicative valuation convention on a real example. -/
theorem X_notMem_integers_atInfty : (RatFunc.X : RatFunc K) ∉ (atInfty K).integers := by
  rw [mem_integers, atInfty_v, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  norm_num

/-- `1 / t` vanishes at infinity, so it lies in the valuation ring of the place at infinity. -/
theorem inv_X_mem_integers_atInfty : (RatFunc.X : RatFunc K)⁻¹ ∈ (atInfty K).integers := by
  rw [mem_integers, show (RatFunc.X : RatFunc K)⁻¹ = 1 / RatFunc.X from (one_div _).symm,
    atInfty_v, RatFunc.inftyValuation.X_inv, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

/-- Every rational function with no pole at infinity differs from a constant by a rational
function that vanishes at infinity: if `f = p / q` with `deg p ≤ deg q`, then the constant is the
quotient of `p` by the monic polynomial `q`. -/
theorem exists_inftyValuation_sub_lt_one {f : RatFunc K} (hf : RatFunc.inftyValuation K f ≤ 1) :
    ∃ c : K, RatFunc.inftyValuation K (f - algebraMap K (RatFunc K) c) < 1 := by
  have hq := RatFunc.monic_denom f
  have hq0 : algebraMap (Polynomial K) (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq.ne_zero
  have hdeg : f.num.natDegree ≤ f.denom.natDegree := by
    by_cases h0 : f = 0
    · simp [h0]
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K h0,
      ← WithZero.exp_zero, WithZero.exp_le_exp, RatFunc.intDegree] at hf
    omega
  obtain ⟨c, hc⟩ : ∃ c, f.num /ₘ f.denom = Polynomial.C c :=
    ⟨_, Polynomial.eq_C_of_natDegree_eq_zero (by
      rw [Polynomial.natDegree_divByMonic _ hq]; omega)⟩
  refine ⟨c, ?_⟩
  have hsplit := congrArg (algebraMap (Polynomial K) (RatFunc K))
    (Polynomial.modByMonic_add_div f.num f.denom)
  rw [hc, map_add, map_mul, RatFunc.algebraMap_C] at hsplit
  have hfq : f * algebraMap (Polynomial K) (RatFunc K) f.denom =
      algebraMap (Polynomial K) (RatFunc K) f.num := by
    rw [eq_comm, ← div_eq_iff hq0]
    exact RatFunc.num_div_denom f
  have key : f - algebraMap K (RatFunc K) c =
      algebraMap (Polynomial K) (RatFunc K) (f.num %ₘ f.denom) /
        algebraMap (Polynomial K) (RatFunc K) f.denom := by
    rw [eq_div_iff hq0, RatFunc.algebraMap_eq_C]
    linear_combination hfq - hsplit
  rw [key, map_div₀]
  by_cases hr : f.num %ₘ f.denom = 0
  · simp [hr]
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation.polynomial _ hr, RatFunc.inftyValuation.polynomial _ hq.ne_zero,
    ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp, sub_neg, Nat.cast_lt]
  exact Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_modByMonic_lt _ hq)

/-- The place at infinity of the projective line has degree one: its residue field is `K`. -/
theorem degree_atInfty : (atInfty K).degree = 1 :=
  degree_eq_one_of_forall_exists fun _ hf => exists_inftyValuation_sub_lt_one K hf

end Place

/-- The `Place` encoding is inhabited by a genuine geometric place: the projective line has the
place at infinity. -/
example : Nonempty (Place K (RatFunc K)) := by
  classical exact ⟨Place.atInfty K⟩

/-- A trivial extension has no places: a valuation trivial on `K` is then trivial everywhere, so
it cannot be surjective. -/
theorem isEmpty_place_self : IsEmpty (Place K K) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨f, hf⟩ := P.surjective (exp 1)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have h1 := Valuation.IsTrivialOn.eq_one (A := K) (v := P.v) f hf0
  rw [Algebra.algebraMap_self_apply, hf, ← WithZero.exp_zero] at h1
  exact one_ne_zero (WithZero.exp_injective h1)

end FunctionField
