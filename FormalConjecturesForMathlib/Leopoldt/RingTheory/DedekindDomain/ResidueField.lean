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

public import Mathlib

/-!
# The residue field of the completed integers `𝓞_v` is finite

Let `A` be a Dedekind domain with fraction field `K` and let `v` be a nonzero prime of `A`. The
ring `𝓞_v = v.adicCompletionIntegers K` is a local ring, and `A` is dense in it: every
element of `𝓞_v` is congruent modulo the maximal ideal to an element of `A`. Hence
`A → 𝓞_v / 𝔪_v` is surjective, and the residue field of `𝓞_v` is finite whenever `A ⧸ v` is,
for instance for the ring of integers of a number field.

Mathlib `v4.33.1` has the approximation statements on `K` itself
(`IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer`) but says nothing about
the residue field of `v.adicCompletionIntegers K`; the FLT project proves the finiteness
through a ring isomorphism `A ⧸ v ≃+* 𝓞_v / 𝔪_v` (`FLT/DedekindDomain/AdicValuation.lean`,
K. Buzzard and S. Mercuri). Only surjectivity is needed here, so this file transports the
mathlib approximation across the completion and quotients.

## Main results

* `exists_valued_sub_algebraMap_lt_one`: every element of `𝓞_v` is congruent to an element of
  `A` modulo `𝔪_v`.
* `mem_maximalIdeal_adicCompletionIntegers_iff`: `𝔪_v` is the set of elements of valuation `< 1`.
* `residue_comp_algebraMap_surjective`: `A → 𝓞_v / 𝔪_v` is surjective.
* `finite_residueField_of_finite_quotient`: the residue field of `𝓞_v` is finite when `A ⧸ v`
  is, and `finite_residueField_adicCompletionIntegers`, the instance for `A` finite free over
  `ℤ`.
-/

@[expose] public section

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K] (v : HeightOneSpectrum A)

/-- `A` is dense in `𝓞_v` modulo the maximal ideal: every `x ∈ 𝓞_v` is congruent to some
`a ∈ A` modulo `𝔪_v`. This is `exists_valuation_sub_lt_of_integer` transported along the
completion: `K` is dense in `K_v`, and a `K`-approximation of `x` is itself `v`-integral. -/
theorem exists_valued_sub_algebraMap_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : A, Valued.v ((x : v.adicCompletion K) - algebraMap A (v.adicCompletion K) a) < 1 := by
  have hcoe : ∀ y : K, Valued.v (algebraMap K (v.adicCompletion K) y) = v.valuation K y :=
    fun y ↦ valuedAdicCompletion_eq_valuation' v y
  have h1 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict 1 ≠ 0 := by simp
  have hs : {y : v.adicCompletion K |
      Valued.v.restrict (y - (x : v.adicCompletion K)) < Valued.v.restrict 1} ∈
      nhds (x : v.adicCompletion K) := Valued.mem_nhds.2 ⟨Units.mk0 _ h1, subset_rfl⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap K v).mem_nhds hs
  rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff, map_one] at hk
  have hxk : Valued.v ((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) k) < 1 := by
    rwa [Valuation.map_sub_swap]
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← hcoe, ← sub_add_cancel (algebraMap K (v.adicCompletion K) k) (x : v.adicCompletion K)]
    exact (Valuation.map_add _ _ _).trans (max_le hk.le x.2)
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hk1 1
  rw [Units.val_one, Valuation.map_sub_swap] at ha
  refine ⟨a, ?_⟩
  have hka : Valued.v (algebraMap K (v.adicCompletion K) k
      - algebraMap A (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply A K (v.adicCompletion K), ← map_sub, hcoe]
    exact ha
  rw [← sub_add_sub_cancel _ (algebraMap K (v.adicCompletion K) k) _]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt hxk hka)

/-- The image of `a : A` in `𝓞_v`, viewed in `K_v`, is the image of `a` under `A → K_v`. This
is `algebraMap_adicCompletionIntegers_apply` in the normal form that writes the `K_v`-valued
map as a single `algebraMap` rather than a coercion of `algebraMap A K a`. -/
@[simp]
theorem coe_algebraMap_adicCompletionIntegers (a : A) :
    ((algebraMap A (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap A (v.adicCompletion K) a := rfl

/-- The maximal ideal of `𝓞_v` is the set of elements of valuation `< 1`. This is
`Valuation.mem_maximalIdeal_iff` for `Valued.v`, using that `v.adicCompletionIntegers K` is by
definition `Valued.v.valuationSubring`. -/
theorem mem_maximalIdeal_adicCompletionIntegers_iff {x : v.adicCompletionIntegers K} :
    x ∈ maximalIdeal (v.adicCompletionIntegers K) ↔ Valued.v (x : v.adicCompletion K) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

/-- The composite `A → 𝓞_v → 𝓞_v / 𝔪_v` is surjective. Note that it is *not* injective in
general: its kernel is `v` itself, which is what makes the residue field a quotient of
`A ⧸ v` rather than a copy of it. -/
theorem residue_comp_algebraMap_surjective :
    Function.Surjective ((residue (v.adicCompletionIntegers K)).comp
      (algebraMap A (v.adicCompletionIntegers K))) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := exists_valued_sub_algebraMap_lt_one K v x
  refine ⟨a, Ideal.Quotient.eq.2 ((mem_maximalIdeal_adicCompletionIntegers_iff K v).2 ?_)⟩
  rwa [show ((algebraMap A (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap A (v.adicCompletion K) a - (x : v.adicCompletion K) by
    rw [AddSubgroupClass.coe_sub, coe_algebraMap_adicCompletionIntegers],
    Valuation.map_sub_swap]

/-- An element of `A` has valuation `< 1` in `K_v` exactly when it lies in `v`. This is
`intValuation_lt_one_iff_mem` transported to the completion. -/
theorem valuedAdicCompletion_lt_one_iff_mem {a : A} :
    Valued.v (algebraMap A (v.adicCompletion K) a) < 1 ↔ a ∈ v.asIdeal := by
  rw [show Valued.v (algebraMap A (v.adicCompletion K) a) = v.intValuation a by
    simp [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap],
    intValuation_lt_one_iff_mem]

/-- The residue field of `𝓞_v` is finite whenever `A ⧸ v` is: it is a quotient of `A ⧸ v`,
because `A → 𝓞_v / 𝔪_v` is surjective and kills `v`. The hypothesis is on `A`, not on `𝓞_v`. -/
theorem finite_residueField_of_finite_quotient [Finite (A ⧸ v.asIdeal)] :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  refine Finite.of_surjective (Ideal.Quotient.lift v.asIdeal
    ((residue (v.adicCompletionIntegers K)).comp (algebraMap A (v.adicCompletionIntegers K)))
    ?_) ?_
  · intro a ha
    rwa [RingHom.comp_apply, residue_eq_zero_iff, mem_maximalIdeal_adicCompletionIntegers_iff,
      coe_algebraMap_adicCompletionIntegers, valuedAdicCompletion_lt_one_iff_mem]
  · intro z
    obtain ⟨a, ha⟩ := residue_comp_algebraMap_surjective K v z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- The residue field of `𝓞_v` is finite for `A` finite free over `ℤ`, e.g. `A = 𝓞 K` the ring
of integers of a number field. Those are exactly the hypotheses of
`Ideal.finiteQuotientOfFreeOfNeBot`, which supplies `Finite (A ⧸ v.asIdeal)`. -/
instance finite_residueField_adicCompletionIntegers [Module.Free ℤ A] [Module.Finite ℤ A] :
    Finite (ResidueField (v.adicCompletionIntegers K)) :=
  have : Finite (A ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  finite_residueField_of_finite_quotient K v

end IsDedekindDomain.HeightOneSpectrum
