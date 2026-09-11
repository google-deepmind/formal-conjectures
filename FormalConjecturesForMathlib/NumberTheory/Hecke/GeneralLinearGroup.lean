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

public import FormalConjecturesForMathlib.NumberTheory.Hecke.HeckePair
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

/-!
# `GL n` of an integral domain is a Hecke subgroup of `GL n` of its fraction field

The bridge between the abstract theory of Hecke pairs and the group whose Hecke algebra carries
the Satake parameters. The two instances in mind, both proved at the end of this file, are
`GL n ℤ ≤ GL n ℚ`, the classical Hecke pair of modular forms, and `GL n ℤ_[p] ≤ GL n ℚ_[p]`,
in which the spherical Hecke algebra at `p` and its Satake parameters live.

The proof is by congruence subgroups. Given `g` in `GL n F`, clearing denominators in the
entries of `g` and of `g⁻¹` produces `a ≠ 0` in `R` with `a • g` and `a • g⁻¹` integral, and
then conjugation by `g` carries the principal congruence subgroup of level `a ^ 2` into
`GL n R`. That congruence subgroup has finite index as soon as the residue ring `R ⧸ (a ^ 2)`
is finite, which is the one arithmetic hypothesis needed; it fails, and so does the conclusion,
for a ring like `k[[t]]` with `k` infinite. For `ℤ` the residue rings are finite outright; for
`ℤ_[p]`, a discrete valuation ring, every nonzero `a` is associated to a power of `p`, and
`ℤ_[p] ⧸ (p ^ n) ≃ ZMod (p ^ n)` is finite.

## Main declarations

* `Matrix.GeneralLinearGroup.congruenceSubgroup`: the principal congruence subgroup of level
  an ideal.
* `Matrix.GeneralLinearGroup.finiteIndex_congruenceSubgroup`: it has finite index when the
  residue ring is finite.
* `Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup`: `GL n R` is a Hecke subgroup of
  `GL n F` when every nonzero residue ring of `R` is finite.
* `Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup_int` and
  `Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup_padic`: the two instances.
-/

open scoped Pointwise

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The **principal congruence subgroup** of level `I`: the matrices in `GL n R` congruent to
the identity modulo `I`. -/
def congruenceSubgroup (I : Ideal R) : Subgroup (GL n R) :=
  MonoidHom.ker (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I))

theorem mem_congruenceSubgroup {I : Ideal R} {g : GL n R} :
    g ∈ congruenceSubgroup I ↔
      ∀ i j, (g : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  rw [congruenceSubgroup, MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun u : GL n (R ⧸ I) => (u : Matrix n n (R ⧸ I)) i j) h
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite,
      ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.eq_zero_iff_mem] using this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using this

/-- The principal congruence subgroup has finite index when the residue ring is finite. -/
instance finiteIndex_congruenceSubgroup (I : Ideal R) [Finite (R ⧸ I)] :
    (congruenceSubgroup (n := n) I).FiniteIndex := by
  have : Finite (GL n (R ⧸ I)) := inferInstance
  have : Finite (GL n R ⧸ congruenceSubgroup (n := n) I) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)))
  exact ⟨Subgroup.index_ne_zero_of_finite⟩

/-! ### A concrete instance

The classical principal congruence subgroup `Γ(N) ≤ GL n ℤ` has finite index. This is the
`R = ℤ` case, and checks that the `Finite (R ⧸ I)` hypothesis is one that real examples meet. -/

example (N : ℕ) [NeZero N] :
    (congruenceSubgroup (n := Fin 2) (Ideal.span {(N : ℤ)})).FiniteIndex := by
  have : Finite (ℤ ⧸ Ideal.span {(N : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod N).symm.toEquiv
  infer_instance

section Integral

variable {S : Type*} [CommRing S]

theorem map_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) := by
  intro g h hgh
  ext i j
  have h2 := congrArg (fun u : GL n S => (u : Matrix n n S) i j) hgh
  simp only [Matrix.GeneralLinearGroup.map_apply] at h2
  exact hf h2

variable (n R)
variable (F : Type*) [Field F] [Algebra R F]

/-- `GL n R` viewed inside `GL n F`. -/
def integralSubgroup : Subgroup (GL n F) :=
  (Matrix.GeneralLinearGroup.map (algebraMap R F)).range

variable {n R F}

theorem mem_integralSubgroup_iff {g : GL n F} :
    g ∈ integralSubgroup n R F ↔
      ∃ u : GL n R, Matrix.GeneralLinearGroup.map (algebraMap R F) u = g :=
  Iff.rfl

/-- A matrix over `F` all of whose entries come from `R`. -/
def HasIntegralEntries (M : Matrix n n F) : Prop :=
  ∀ i j, M i j ∈ (algebraMap R F).range

namespace HasIntegralEntries

variable {M N : Matrix n n F}

omit [DecidableEq n] in
theorem mul (hM : HasIntegralEntries (R := R) M) (hN : HasIntegralEntries (R := R) N) :
    HasIntegralEntries (R := R) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

omit [Fintype n] [DecidableEq n] in
theorem add (hM : HasIntegralEntries (R := R) M) (hN : HasIntegralEntries (R := R) N) :
    HasIntegralEntries (R := R) (M + N) := fun i j =>
  Subring.add_mem _ (hM i j) (hN i j)

omit [Fintype n] in
theorem one : HasIntegralEntries (R := R) (1 : Matrix n n F) := fun i j => by
  rw [Matrix.one_apply]
  split <;> simp

end HasIntegralEntries

/-- A matrix over `F` which is integral and has integral inverse comes from `GL n R`. -/
theorem mem_integralSubgroup_of_integral {g : GL n F}
    (hinj : Function.Injective (algebraMap R F))
    (hg : HasIntegralEntries (R := R) (g : Matrix n n F))
    (hg' : HasIntegralEntries (R := R) ((g⁻¹ : GL n F) : Matrix n n F)) :
    g ∈ integralSubgroup n R F := by
  choose M hM using hg
  choose N hN using hg'
  have hmapinj : Function.Injective ((algebraMap R F).mapMatrix (m := n)) := by
    intro x y hxy
    ext i j
    exact hinj (congrArg (fun P : Matrix n n F => P i j) hxy)
  have hMF : (algebraMap R F).mapMatrix (Matrix.of M) = (g : Matrix n n F) := by
    ext i j; exact hM i j
  have hNF : (algebraMap R F).mapMatrix (Matrix.of N) = ((g⁻¹ : GL n F) : Matrix n n F) := by
    ext i j; exact hN i j
  have h1 : Matrix.of M * Matrix.of N = 1 := by
    apply hmapinj
    rw [map_mul, hMF, hNF, map_one]
    exact g.mul_inv
  have h2 : Matrix.of N * Matrix.of M = 1 := by
    apply hmapinj
    rw [map_mul, hMF, hNF, map_one]
    exact g.inv_mul
  refine ⟨⟨Matrix.of M, Matrix.of N, h1, h2⟩, ?_⟩
  ext i j
  simpa [Matrix.GeneralLinearGroup.map_apply] using hM i j

section Denominators

variable [IsDomain R] [IsFractionRing R F]

/-- Clearing denominators: some nonzero `a : R` makes both `g` and `g⁻¹` integral. -/
theorem exists_common_denom (g : GL n F) :
    ∃ a : R, a ≠ 0 ∧ HasIntegralEntries (R := R) (a • (g : Matrix n n F)) ∧
      HasIntegralEntries (R := R) (a • ((g⁻¹ : GL n F) : Matrix n n F)) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun x : (n × n) ⊕ (n × n) => Sum.elim
      (fun p : n × n => (g : Matrix n n F) p.1 p.2)
      (fun p : n × n => ((g⁻¹ : GL n F) : Matrix n n F) p.1 p.2) x)
  refine ⟨(b : R), nonZeroDivisors.coe_ne_zero b, fun i j => ?_, fun i j => ?_⟩
  · have h := hb (Sum.inl (i, j))
    obtain ⟨r, hr⟩ := h
    exact ⟨r, by simpa using hr⟩
  · have h := hb (Sum.inr (i, j))
    obtain ⟨r, hr⟩ := h
    exact ⟨r, by simpa using hr⟩

omit [IsDomain R] [IsFractionRing R F] in
/-- The key computation: if `a` clears the denominators of `g` and `g⁻¹`, then conjugation by
`g` carries the congruence subgroup of level `a ^ 2` into the integral matrices. Writing
`k = 1 + a ^ 2 * m`, the conjugate is `1 + (a * g) * m * (a * g⁻¹)`, in which every factor is
integral. -/
theorem hasIntegralEntries_conj {a : R} {g : GL n F}
    (hg : HasIntegralEntries (R := R) (a • (g : Matrix n n F)))
    (hg' : HasIntegralEntries (R := R) (a • ((g⁻¹ : GL n F) : Matrix n n F)))
    {k : GL n R} (hk : k ∈ congruenceSubgroup (n := n) (Ideal.span {a * a})) :
    HasIntegralEntries (R := R) ((g : Matrix n n F) *
      ((Matrix.GeneralLinearGroup.map (algebraMap R F) k : GL n F) : Matrix n n F) *
      ((g⁻¹ : GL n F) : Matrix n n F)) := by
  have hmem := mem_congruenceSubgroup.mp hk
  choose m hm using fun i j => Ideal.mem_span_singleton'.mp (hmem i j)
  set MF : Matrix n n F := Matrix.of fun i j => algebraMap R F (m i j) with hMFdef
  have hMF : HasIntegralEntries (R := R) MF := fun i j => ⟨m i j, rfl⟩
  have hk_eq : ((Matrix.GeneralLinearGroup.map (algebraMap R F) k : GL n F) : Matrix n n F)
      = 1 + (a * a) • MF := by
    ext i j
    have hij : (k : Matrix n n R) i j = (1 : Matrix n n R) i j + m i j * (a * a) := by
      rw [hm i j]; ring
    simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.add_apply, Matrix.smul_apply,
      hMFdef, Matrix.of_apply]
    rw [hij, map_add, map_mul, Algebra.smul_def]
    simp [Matrix.one_apply]
    ring
  rw [hk_eq]
  have hmulinv : (g : Matrix n n F) * ((g⁻¹ : GL n F) : Matrix n n F) = 1 := g.mul_inv
  have e2 : (g : Matrix n n F) * (1 + (a * a) • MF) * ((g⁻¹ : GL n F) : Matrix n n F)
      = 1 + (a • (g : Matrix n n F)) * MF * (a • ((g⁻¹ : GL n F) : Matrix n n F)) := by
    rw [mul_add, mul_one, add_mul, hmulinv]
    congr 1
    simp [smul_smul, Matrix.mul_assoc]
  rw [e2]
  exact HasIntegralEntries.one.add ((hg.mul hMF).mul hg')

omit [IsDomain R] [IsFractionRing R F] in
/-- Conjugation by `g` carries the congruence subgroup of level `a ^ 2` into `GL n R`. -/
theorem conj_map_mem_integralSubgroup {a : R} {g : GL n F}
    (hinj : Function.Injective (algebraMap R F))
    (hg : HasIntegralEntries (R := R) (a • (g : Matrix n n F)))
    (hg' : HasIntegralEntries (R := R) (a • ((g⁻¹ : GL n F) : Matrix n n F)))
    {k : GL n R} (hk : k ∈ congruenceSubgroup (n := n) (Ideal.span {a * a})) :
    g * (Matrix.GeneralLinearGroup.map (algebraMap R F) k) * g⁻¹ ∈ integralSubgroup n R F := by
  refine mem_integralSubgroup_of_integral hinj ?_ ?_
  · simpa using hasIntegralEntries_conj hg hg' hk
  · have hinvform : (g * (Matrix.GeneralLinearGroup.map (algebraMap R F) k) * g⁻¹)⁻¹
        = g * (Matrix.GeneralLinearGroup.map (algebraMap R F) k⁻¹) * g⁻¹ := by
      simp [mul_assoc]
    rw [hinvform]
    simpa using hasIntegralEntries_conj hg hg' (inv_mem hk)

end Denominators

section HeckePair

variable [IsDomain R] [IsFractionRing R F]

/-- **`GL n R` is a Hecke subgroup of `GL n F`**, when every nonzero residue ring of `R` is
finite. This is the hypothesis satisfied by `ℤ` and by the ring of integers of a
nonarchimedean local field, and it cannot be dropped: for `R = k⟦t⟧` with `k` infinite,
`GL n R` is not a Hecke subgroup of `GL n (k⦅t⦆)`. -/
theorem isHeckePair_integralSubgroup
    (hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})) :
    Subgroup.IsHeckePair (integralSubgroup n R F) := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hφinj := map_injective (n := n) hinj
  refine Subgroup.isHeckePair_of_relIndex fun g => ?_
  obtain ⟨a, ha, hga, hga'⟩ := exists_common_denom (n := n) (R := R) g
  have : Finite (R ⧸ Ideal.span {a * a}) := hfin _ (mul_ne_zero ha ha)
  set e : GL n R ≃* ↥(integralSubgroup n R F) := MonoidHom.ofInjective hφinj with he
  set H := (ConjAct.toConjAct g • integralSubgroup n R F).subgroupOf (integralSubgroup n R F)
    with hH
  have hle : congruenceSubgroup (n := n) (Ideal.span {a * a}) ≤
      H.comap (e : GL n R →* ↥(integralSubgroup n R F)) := by
    intro k hk
    simp only [Subgroup.mem_comap, hH, Subgroup.mem_subgroupOf]
    show (↑(e k) : GL n F) ∈ ConjAct.toConjAct g • integralSubgroup n R F
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hmain := conj_map_mem_integralSubgroup (g := g⁻¹) hinj hga' (by simpa using hga) hk
    have hcoe : ((e k : ↥(integralSubgroup n R F)) : GL n F)
        = Matrix.GeneralLinearGroup.map (algebraMap R F) k := rfl
    rw [hcoe]
    simpa [ConjAct.smul_def] using hmain
  have hdvd := Subgroup.index_dvd_of_le hle
  have hne : (congruenceSubgroup (n := n) (Ideal.span {a * a})).index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hcomap : (H.comap (e : GL n R →* ↥(integralSubgroup n R F))).index = H.index :=
    Subgroup.index_comap_of_surjective _ e.surjective
  rw [Subgroup.relIndex, ← hH, ← hcomap]
  intro hzero
  exact hne (Nat.eq_zero_of_zero_dvd (hzero ▸ hdvd))

/-- The classical Hecke pair: `GL n ℤ` inside `GL n ℚ`. -/
theorem isHeckePair_integralSubgroup_int :
    Subgroup.IsHeckePair (integralSubgroup n ℤ ℚ) :=
  isHeckePair_integralSubgroup fun a ha => by
    have : NeZero a := ⟨ha⟩
    infer_instance

end HeckePair

end Integral

end Matrix.GeneralLinearGroup

/-! ### The `p`-adic Hecke pair

`GL n ℤ_[p]` is a Hecke subgroup of `GL n ℚ_[p]`. This is the instance of
`Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup` in which the spherical Hecke algebra
and its Satake parameters live, so it is what makes those definitions concrete rather than
hypothetical. The one thing to check is that the residue rings of `ℤ_[p]` are finite. -/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The residue rings of `ℤ_[p]` are finite. -/
theorem finite_quotient_span_singleton {a : ℤ_[p]} (ha : a ≠ 0) :
    Finite (ℤ_[p] ⧸ Ideal.span {a}) := by
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
    (PadicInt.irreducible_p (p := p))
  have hspan : Ideal.span {a} = Ideal.span {(p : ℤ_[p]) ^ n} :=
    Ideal.span_singleton_eq_span_singleton.mpr hn
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  rw [hspan, ← PadicInt.ker_toZModPow n]
  exact Finite.of_equiv _ (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow n))).symm.toEquiv

end PadicInt

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]

/-- **`GL n ℤ_[p]` is a Hecke subgroup of `GL n ℚ_[p]`**, so the spherical Hecke operators and
Satake parameters exist for it with no further hypotheses. -/
theorem isHeckePair_integralSubgroup_padic :
    Subgroup.IsHeckePair (integralSubgroup n ℤ_[p] ℚ_[p]) :=
  isHeckePair_integralSubgroup fun _ ha => PadicInt.finite_quotient_span_singleton ha

end Matrix.GeneralLinearGroup
