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

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.StandardSmooth

import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Krull dimension along a quasi-finite or standard smooth ring map

A quasi-finite algebra has no room for a strictly larger chain of primes than its base, so the
comparison map on prime spectra is strictly monotone and the Krull dimension does not grow. When
the algebra is also flat, the height of a prime is the height of the prime below it.

A standard smooth ring map of relative dimension `d` factors through a polynomial ring in `d`
variables, which bounds the Krull dimension of the target by that of the source plus `d`. Over a
field in which every maximal ideal of a finitely generated algebra has residue field the field
itself — a Jacobson-ring argument, applied here to `ℂ` — the bound is an equality.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Contraction of prime ideals is strictly monotone for a quasi-finite algebra. -/
lemma QuasiFinite.strictMono_primeSpectrumComap [QuasiFinite R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  have hle : P.asIdeal.under R ≤ Q.asIdeal.under R := Ideal.comap_mono hPQ.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq' : P.asIdeal.under R = Q.asIdeal.under R := by
    simpa [Ideal.under] using congrArg PrimeSpectrum.asIdeal heq
  have hPQeq : P.asIdeal = Q.asIdeal :=
    QuasiFinite.eq_of_le_of_under_eq (R := R) P.asIdeal Q.asIdeal hPQ.le heq'
  exact hPQ.ne (PrimeSpectrum.ext hPQeq)

/-- A quasi-finite algebra cannot have larger Krull dimension than its base. -/
lemma QuasiFinite.ringKrullDim_le [QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  exact Order.krullDim_le_of_strictMono _ QuasiFinite.strictMono_primeSpectrumComap

/-- A flat quasi-finite algebra preserves the height of every prime under contraction. -/
lemma QuasiFinite.height_eq_height_under [QuasiFinite R S] [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  calc
    P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum S) :=
      PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum S)
    _ = Order.height
        (PrimeSpectrum.comap (algebraMap R S) (⟨P, inferInstance⟩ : PrimeSpectrum S)) := by
      apply Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
        QuasiFinite.strictMono_primeSpectrumComap
      intro Q p hp
      have hp' : p.asIdeal < Q.asIdeal.under R := by
        have hp'' : p.asIdeal <
            (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal := hp
        simpa only [PrimeSpectrum.comap_asIdeal] using hp''
      obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        Q.asIdeal.exists_ideal_lt_liesOver_of_lt
          (R := R) (p := p.asIdeal) (q := Q.asIdeal.under R) hp'
      refine ⟨⟨Q', hQ'prime⟩, hQ'Q, ?_⟩
      apply PrimeSpectrum.ext
      simpa [Ideal.under] using hQ'over.over.symm
    _ = (P.under R).height := by
      rw [show (P.under R) =
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S)).asIdeal from rfl]
      exact (PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S))).symm

end Algebra

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The contraction of a maximal ideal along a finite-type map from a Jacobson ring is maximal. -/
lemma FiniteType.isMaximal_comap_of_isJacobsonRing [IsJacobsonRing R] {f : R →+* S}
    (hf : f.FiniteType) (P : Ideal S) [P.IsMaximal] : (P.comap f).IsMaximal := by
  let K := S ⧸ P
  let q : S →+* K := Ideal.Quotient.mk P
  let : Field K := Ideal.Quotient.field P
  have hft : (q.comp f).FiniteType := hf.comp_surjective Ideal.Quotient.mk_surjective
  have hfin : (q.comp f).Finite :=
    RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft
  have hmax : ((⊥ : Ideal K).comap (q.comp f)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (q.comp f) hfin.to_isIntegral ⊥
  change (((⊥ : Ideal K).comap q).comap f).IsMaximal at hmax
  have hq : (⊥ : Ideal K).comap q = P := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rwa [hq] at hmax

/-- A standard-smooth algebra of relative dimension `d` has Krull dimension at most the
dimension of the base plus `d`. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_le_add {f : R →+* S} {d : ℕ}
    [IsNoetherianRing R]
    (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim S ≤ ringKrullDim R + d := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) R) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) R) S :=
    RingHom.etale_algebraMap.mp hg
  calc
    ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin d) R) :=
      Algebra.QuasiFinite.ringKrullDim_le
    _ = ringKrullDim R + d := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_fin]

/-- A standard-smooth complex algebra of relative dimension `d` has Krull dimension at most
`d`. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_le_complex {S : Type*} [CommRing S]
    {f : ℂ →+* S} {d : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim S ≤ d := by
  simpa only [ringKrullDim_eq_zero_of_field, WithBot.coe_zero, zero_add] using
    hf.ringKrullDim_le_add

end RingHom

namespace MvPolynomial

/-- Every maximal ideal of a polynomial ring in `d` variables over a field has height `d`. -/
lemma height_eq_fin_of_isMaximal (K : Type*) [Field K] (d : ℕ)
    (P : Ideal (MvPolynomial (Fin d) K)) [P.IsMaximal] : P.height = d := by
  induction d with
  | zero =>
      have hle : (↑P.height : WithBot ℕ∞) ≤
          ringKrullDim (MvPolynomial (Fin 0) K) :=
        Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, Nat.card_fin, Nat.cast_zero, add_zero] at hle
      exact le_antisymm (WithBot.coe_le_coe.mp hle) bot_le
  | succ n ih =>
      let e : MvPolynomial (Fin (n + 1)) K ≃+* Polynomial (MvPolynomial (Fin n) K) :=
        (MvPolynomial.finSuccEquiv K n).toRingEquiv
      let Q : Ideal (Polynomial (MvPolynomial (Fin n) K)) := P.map e
      let : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
      have hunder : (Q.under (MvPolynomial (Fin n) K)).IsMaximal := by
        change (Q.comap (Polynomial.C : MvPolynomial (Fin n) K →+*
          Polynomial (MvPolynomial (Fin n) K))).IsMaximal
        exact Polynomial.isMaximal_comap_C_of_isJacobsonRing
          (R := MvPolynomial (Fin n) K) Q
      calc
        P.height = Q.height := (RingEquiv.height_map e P).symm
        _ = (Q.under (MvPolynomial (Fin n) K)).height + 1 :=
          Polynomial.height_eq_height_add_one _ Q
        _ = n + 1 := by rw [ih (Q.under (MvPolynomial (Fin n) K))]

end MvPolynomial

namespace RingHom

/-- A nonzero standard-smooth complex algebra of relative dimension `d` has Krull dimension
exactly `d`.

This global equality does not by itself give the pointwise catenary dimension formula. -/
lemma IsStandardSmoothOfRelativeDimension.ringKrullDim_eq_complex {S : Type*} [CommRing S]
    [Nontrivial S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d) : ringKrullDim S = d := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  obtain ⟨P, hP⟩ := Ideal.exists_maximal S
  let : P.IsMaximal := hP
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) ℂ) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hunder : (P.under (MvPolynomial (Fin d) ℂ)).IsMaximal :=
    hfiniteType.isMaximal_comap_of_isJacobsonRing P
  have hheight : P.height = d := by
    rw [Algebra.QuasiFinite.height_eq_height_under (R := MvPolynomial (Fin d) ℂ)]
    exact MvPolynomial.height_eq_fin_of_isMaximal ℂ d
      (P.under (MvPolynomial (Fin d) ℂ))
  apply le_antisymm hf.ringKrullDim_le_complex
  change (↑(d : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S
  have hlower : (↑P.height : WithBot ℕ∞) ≤ ringKrullDim S :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  rwa [← hheight]

end RingHom
