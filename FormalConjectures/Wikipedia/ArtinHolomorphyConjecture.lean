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

public import FormalConjecturesUtil

/-!
# Emil Artin's Holomorphy Conjecture for Non-Abelian Artin L-Functions

Given a finite Galois extension $L / K$ of algebraic number fields with group
$G = \operatorname{Gal}(L / K)$ and a finite-dimensional nontrivial irreducible complex
representation $\rho : G \to \operatorname{GL}(V)$, Emil Artin (1923, 1930) defined $L(s, \rho)$
on the half-plane $\operatorname{Re}(s) > 1$ via the Euler product over nonzero prime ideals
$\mathfrak{p}$ of $\mathcal{O}_K$ with local factors
$\det(I - N(\mathfrak{p})^{-s}
\rho(\operatorname{Frob}_{\mathfrak{P}})|_{V^{I_{\mathfrak{P}}}})^{-1}$.

Richard Brauer (1947) used character induction from elementary subgroups to establish meromorphic
continuation across $\mathbb{C}$. Artin's holomorphy conjecture predicts that whenever $\rho$ is
irreducible and nontrivial, $L(s, \rho)$ extends to an entire function on $\mathbb{C}$. Known cases
include monomial representations, solvable two-dimensional representations (Langlands 1980;
Tunnell 1981), and odd two-dimensional representations over $\mathbb{Q}$ via Serre's modularity
conjecture (Khare–Wintenberger 2009), while general icosahedral and higher-dimensional cases remain
open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Artin_conjecture_(L-functions))
- E. Artin, *Über eine neue Art von L-Reihen*, Abh. Math. Sem. Univ. Hamburg **3** (1923/1924),
  89–108.
- E. Artin, *Zur Theorie der L-Reihen mit allgemeinen Gruppencharakteren*, Abh. Math. Sem. Univ.
  Hamburg **8** (1930), 292–306.
- R. Brauer, *On Artin's L-series with general group characters*, Ann. of Math. (2) **48** (1947),
  502–514.
-/

@[expose] public section

namespace ArtinHolomorphyConjecture

open scoped Classical in
/-- For a prime $\mathfrak{P}$ of $\mathcal{O}_L$, the average of $\rho(\sigma)$ across all
relative arithmetic Frobenius elements $\sigma \in \operatorname{Gal}(L / K)$ at $\mathfrak{P}$
(satisfying $\sigma(x) \equiv x^{N(\mathfrak{p})} \pmod{\mathfrak{P}}$), which equals
$\rho(\sigma_{\mathfrak{P}}) \circ P_{I_{\mathfrak{P}}}$ for the Reynolds projector
$P_{I_{\mathfrak{P}}}$ onto $V^{I_{\mathfrak{P}}}$. -/
noncomputable def inertiaAveragedFrob {K L V : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V)
    (𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) : V →ₗ[ℂ] V :=
  let frobSet : Finset (L ≃ₐ[K] L) := Finset.univ.filter fun σ ↦
    (NumberField.RingOfIntegers.mapAlgEquiv σ).toAlgHom.IsArithFrobAt 𝔓.asIdeal
  ((frobSet.card : ℂ)⁻¹) • ∑ σ ∈ frobSet, ρ σ

open scoped Classical in
/-- The local Euler factor
$\det_V(I - N(\mathfrak{p})^{-s} \rho(\sigma_{\mathfrak{P}}) P_{I_{\mathfrak{P}}})^{-1}$ at a
nonzero prime ideal $\mathfrak{p}$ of $\mathcal{O}_K$ (invariant under choosing any prime
$\mathfrak{P} \mid \mathfrak{p}$ of $\mathcal{O}_L$). -/
noncomputable def artinLocalEulerFactor {K L V : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (s : ℂ) : ℂ :=
  if h : ∃ 𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      𝔓.asIdeal.under (NumberField.RingOfIntegers K) = 𝔭.asIdeal then
    (LinearMap.det (LinearMap.id -
      ((Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) • inertiaAveragedFrob ρ (Classical.choose h)))⁻¹
  else 1

/-- The Artin $L$-function Euler product over all nonzero prime ideals of $\mathcal{O}_K$ on
$\operatorname{Re}(s) > 1$. -/
noncomputable def artinEulerProduct {K L V : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) (s : ℂ) : ℂ :=
  ∏' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
    artinLocalEulerFactor ρ 𝔭 s

/-- Over a trivial extension $K / K$ of any number field $K$, the trivial representation on
$\mathbb{C}$ has `inertiaAveragedFrob = id` at every nonzero prime $\mathfrak{p}$ of
$\mathcal{O}_K$. -/
@[category API, AMS 11]
theorem inertiaAveragedFrob_trivial_self {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    inertiaAveragedFrob (1 : Representation ℂ (K ≃ₐ[K] K) ℂ) 𝔭 = LinearMap.id := by
  classical
  have hfrob : (NumberField.RingOfIntegers.mapAlgEquiv (AlgEquiv.refl : K ≃ₐ[K] K)).toAlgHom
      |>.IsArithFrobAt 𝔭.asIdeal := by
    have : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
    let _ : Field (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
    have : Finite (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
      Ideal.finiteQuotientOfFreeOfNeBot 𝔭.asIdeal 𝔭.ne_bot
    let _ : Fintype (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
    intro x; rw [← Ideal.Quotient.eq, map_pow]; change Ideal.Quotient.mk 𝔭.asIdeal x = _; symm
    convert FiniteField.pow_card (Ideal.Quotient.mk 𝔭.asIdeal x)
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Ideal.quotEquivOfEq (Ideal.ext fun _ => Iff.rfl)).toEquiv
  have hset : (Finset.univ.filter fun σ : K ≃ₐ[K] K =>
      (NumberField.RingOfIntegers.mapAlgEquiv σ).toAlgHom.IsArithFrobAt 𝔭.asIdeal) =
      {AlgEquiv.refl} := by ext σ; simp [Subsingleton.elim σ AlgEquiv.refl, hfrob]
  simp [inertiaAveragedFrob, hset]; rfl

/-- Over $K / K$, the trivial one-dimensional representation has local Artin Euler factor
$(1 - N(\mathfrak{p})^{-s})^{-1}$ at every nonzero prime $\mathfrak{p}$ of $\mathcal{O}_K$. -/
@[category API, AMS 11]
theorem artinLocalEulerFactor_trivial_self {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (s : ℂ) :
    artinLocalEulerFactor (1 : Representation ℂ (K ≃ₐ[K] K) ℂ) 𝔭 s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
  unfold artinLocalEulerFactor
  split_ifs with h
  · have h𝔓 : Classical.choose h = 𝔭 :=
      IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => SetLike.ext_iff.mp h.choose_spec x)
    rw [h𝔓, inertiaAveragedFrob_trivial_self]
    have hlin : (LinearMap.id - ((Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) • LinearMap.id : ℂ →ₗ[ℂ] ℂ) =
        (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) • LinearMap.id := by ext; simp
    rw [hlin, LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
  · exfalso
    exact h ⟨𝔭, Ideal.ext fun _ => Iff.rfl⟩

/-- The sign character on $\mathbb{Z}^\times$ gives a one-dimensional representation on $\mathbb{C}$
that is both irreducible and nontrivial. -/
@[category test, AMS 11]
theorem sign_char_irreducible_nontrivial :
    ∃ χ : Representation ℂ ℤˣ ℂ, χ.IsIrreducible ∧ ¬ χ.IsTrivial := by
  let χ : Representation ℂ ℤˣ ℂ :=
    { toFun := fun u => ((u : ℤ) : ℂ) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun u v => by ext; simp; ring }
  refine ⟨χ, isIrreducible_one_dim χ, fun htriv => ?_⟩
  let _ := htriv
  have h1 : χ (-1 : ℤˣ) (1 : ℂ) = 1 := χ.isTrivial_apply (-1 : ℤˣ) (1 : ℂ)
  change (((-1 : ℤˣ) : ℤ) : ℂ) * 1 = 1 at h1
  norm_num at h1

/-- On the zero-dimensional complex representation space, the Artin Euler product equals $1$. -/
@[category test, AMS 11]
theorem artinEulerProduct_zero_dim (s : ℂ) :
    artinEulerProduct (1 : Representation ℂ (ℚ ≃ₐ[ℚ] ℚ) (Fin 0 → ℂ)) s = 1 := by
  simp [artinEulerProduct, artinLocalEulerFactor, LinearMap.det_eq_one_of_subsingleton]

/-- **Artin's Holomorphy Conjecture** (1923): For every finite Galois extension $L / K$ of algebraic
number fields and every finite-dimensional nontrivial irreducible complex representation $\rho$ of
$\operatorname{Gal}(L / K)$, the Artin $L$-function $L(s, \rho)$ admits an entire analytic
continuation from $\operatorname{Re}(s) > 1$ to all of $\mathbb{C}$. -/
@[category research open, AMS 11]
theorem artin_holomorphy_conjecture {K L V : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) [ρ.IsIrreducible] (hNontriv : ¬ ρ.IsTrivial) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 1 < s.re → F s = artinEulerProduct ρ s := by
  sorry

end ArtinHolomorphyConjecture
