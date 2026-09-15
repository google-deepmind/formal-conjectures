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

public import FormalConjecturesForMathlib.Algebra.Hochschild.Chains
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degree-zero Hochschild homology and normalized traces

A cyclic linear map to any module descends to degree-zero Hochschild homology.
If a linear section is normalized by that trace, its map to Hochschild homology is
bijective exactly when the descended trace is bijective.
-/

@[expose] public section

namespace Hochschild

variable (k A : Type*) [CommRing k] [NonUnitalRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- Degree-zero Hochschild homology, as the cokernel of the degree-one boundary. -/
abbrev HomologyZero := Chains k A 0 ⧸ LinearMap.range (boundary k A 0)

/-- The canonical class in degree-zero Hochschild homology of an algebra element. -/
noncomputable def algebraClassZero : A →ₗ[k] HomologyZero k A :=
  (LinearMap.range (boundary k A 0)).mkQ ∘ₗ (chains0Equiv k A).symm.toLinearMap

variable (V : Type*) [AddCommGroup V] [Module k V]

/-- A cyclic linear map to a module annihilates Hochschild boundaries in degree zero. -/
theorem cyclic_comp_boundary_zero (t : A →ₗ[k] V)
    (ht : ∀ a b : A, t (a * b) = t (b * a)) :
    t ∘ₗ (chains0Equiv k A).toLinearMap ∘ₗ boundary k A 0 = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change t (chains0Equiv k A (boundary k A 0 (PiTensorProduct.tprod k x))) = 0
  rw [chains0Equiv_boundary_zero_tprod]
  simp [ht]

/-- A cyclic linear map descends to degree-zero Hochschild homology. -/
noncomputable def descendTrace (t : A →ₗ[k] V)
    (ht : ∀ a b : A, t (a * b) = t (b * a)) : HomologyZero k A →ₗ[k] V :=
  (LinearMap.range (boundary k A 0)).liftQ (t ∘ₗ (chains0Equiv k A).toLinearMap)
    fun a ha ↦ by
      obtain ⟨c, rfl⟩ := ha
      exact LinearMap.congr_fun (cyclic_comp_boundary_zero k A V t ht) c

@[simp] theorem descendTrace_algebraClassZero (t : A →ₗ[k] V)
    (ht : ∀ a b : A, t (a * b) = t (b * a)) (a : A) :
    descendTrace k A V t ht (algebraClassZero k A a) = t a := by
  simp [descendTrace, algebraClassZero]

/-- A section normalized by the trace is inverse to the descended trace on its image. -/
theorem descendTrace_leftInverse (t : A →ₗ[k] V)
    (ht : ∀ a b : A, t (a * b) = t (b * a)) (s : V →ₗ[k] A)
    (hs : t ∘ₗ s = LinearMap.id) :
    Function.LeftInverse (descendTrace k A V t ht) (algebraClassZero k A ∘ₗ s) := by
  intro v
  change descendTrace k A V t ht (algebraClassZero k A (s v)) = v
  rw [descendTrace_algebraClassZero]
  exact LinearMap.congr_fun hs v

/-- The canonical section map computes degree-zero Hochschild homology exactly when
the normalized trace does. -/
theorem section_bijective_iff_trace_bijective (t : A →ₗ[k] V)
    (ht : ∀ a b : A, t (a * b) = t (b * a)) (s : V →ₗ[k] A)
    (hs : t ∘ₗ s = LinearMap.id) :
    Function.Bijective (algebraClassZero k A ∘ₗ s) ↔
      Function.Bijective (descendTrace k A V t ht) := by
  have h := descendTrace_leftInverse k A V t ht s hs
  constructor
  · intro hf
    exact ⟨fun a b hab ↦ by
      obtain ⟨a', rfl⟩ := hf.2 a
      obtain ⟨b', rfl⟩ := hf.2 b
      exact congrArg (algebraClassZero k A ∘ₗ s)
        ((h a').symm.trans (hab.trans (h b'))), h.surjective⟩
  · intro hg
    refine ⟨h.injective, fun a ↦ ⟨descendTrace k A V t ht a, ?_⟩⟩
    apply hg.1
    exact h _

end Hochschild
