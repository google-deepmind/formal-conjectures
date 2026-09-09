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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import Mathlib.Tactic.LinearCombination

/-!
# Global minimality of Weierstrass equations

Global minimality means integrality over the ring of integers and minimality at every finite prime.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Section VIII.8.
-/

@[expose] public section

namespace WeierstrassCurve

open NumberField IsDedekindDomain

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A Weierstrass equation over a number field is globally minimal if it is integral over the
ring of integers and minimal at every finite prime. -/
@[mk_iff]
class IsGlobalMinimal (W : WeierstrassCurve K) : Prop extends W.IsIntegral (𝓞 K) where
  isMinimal : ∀ v : HeightOneSpectrum (𝓞 K),
    (W.baseChange (v.adicCompletion K)).IsMinimal (v.adicCompletionIntegers K)

attribute [instance] IsGlobalMinimal.isMinimal

/-- A globally minimal equation is integral and minimal at every finite prime. -/
theorem isGlobalMinimal_iff_forall_isMinimal (W : WeierstrassCurve K) :
    W.IsGlobalMinimal ↔ W.IsIntegral (𝓞 K) ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      (W.baseChange (v.adicCompletion K)).IsMinimal (v.adicCompletionIntegers K) :=
  isGlobalMinimal_iff W

end NumberField

section Rat

/-- Integrality over the ring of integers of $\mathbb{Q}$ is integrality over $\mathbb{Z}$. -/
theorem isIntegral_ringOfIntegers_rat_iff (W : WeierstrassCurve ℚ) :
    W.IsIntegral (𝓞 ℚ) ↔ W.IsIntegral ℤ := by
  constructor
  · rintro ⟨⟨W', rfl⟩⟩
    refine ⟨⟨W'.map Rat.ringOfIntegersEquiv.toRingHom, ?_⟩⟩
    ext <;> simp [baseChange]
  · rintro ⟨⟨W', rfl⟩⟩
    refine ⟨⟨W'.map Rat.ringOfIntegersEquiv.symm.toRingHom, ?_⟩⟩
    ext <;> simp [baseChange]

instance (W : WeierstrassCurve ℚ) [W.IsIntegral (𝓞 ℚ)] : W.IsIntegral ℤ :=
  (isIntegral_ringOfIntegers_rat_iff W).1 inferInstance

/-- Every Weierstrass equation over $\mathbb{Q}$ is isomorphic to one with coefficients in
$\mathbb{Z}$. -/
theorem exists_isIntegral_int (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, (C • W).IsIntegral ℤ := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    {W.a₁, W.a₂, W.a₃, W.a₄, W.a₆}
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have key : ∀ (n : ℕ) (a : ℚ), IsLocalization.IsInteger ℤ ((b : ℤ) • a) →
      ∃ r : ℤ, algebraMap ℤ ℚ r = ((b : ℤ) : ℚ) ^ (n + 1) * a := fun n a ⟨r, hr⟩ ↦
    ⟨(b : ℤ) ^ n * r, by push_cast at hr ⊢; linear_combination ((b : ℤ) : ℚ) ^ n * hr⟩
  refine ⟨⟨(Units.mk0 _ hb0)⁻¹, 0, 0, 0⟩, isIntegral_of_exists_lift ℤ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [variableChange_a₁] using key 0 _ (hb _ (by simp))
  · simpa [variableChange_a₂] using key 1 _ (hb _ (by simp))
  · simpa [variableChange_a₃] using key 2 _ (hb _ (by simp))
  · simpa [variableChange_a₄] using key 3 _ (hb _ (by simp))
  · simpa [variableChange_a₆] using key 5 _ (hb _ (by simp))

/-- Every Weierstrass equation over $\mathbb{Q}$ has an integral model with least absolute
discriminant among its integral changes of variables. -/
theorem exists_isIntegral_minimal_abs_Δ (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, (C • W).IsIntegral ℤ ∧
      ∀ C' : VariableChange ℚ, (C' • W).IsIntegral ℤ → |(C • W).Δ| ≤ |(C' • W).Δ| := by
  classical
  have key : ∀ C : VariableChange ℚ, (C • W).IsIntegral ℤ → ∃ n : ℕ, |(C • W).Δ| = n :=
    fun C _ ↦ let ⟨r, hr⟩ := Δ_integral_of_isIntegral ℤ (C • W)
      ⟨r.natAbs, by simp [← hr, Nat.cast_natAbs]⟩
  obtain ⟨C₀, hC₀⟩ := W.exists_isIntegral_int
  have h : ∃ n : ℕ, ∃ C : VariableChange ℚ, (C • W).IsIntegral ℤ ∧ |(C • W).Δ| = n :=
    (key C₀ hC₀).imp fun n hn ↦ ⟨C₀, hC₀, hn⟩
  obtain ⟨C, hC, hn⟩ := Nat.find_spec h
  refine ⟨C, hC, fun C' hC' ↦ ?_⟩
  obtain ⟨n', hn'⟩ := key C' hC'
  rw [hn, hn', Nat.cast_le]
  exact Nat.find_min' h ⟨C', hC', hn'⟩

end Rat

end WeierstrassCurve
