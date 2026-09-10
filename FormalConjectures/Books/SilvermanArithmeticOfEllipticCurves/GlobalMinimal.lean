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
# Global minimal models of elliptic curves

Existence of global minimal models over number fields of class number one, and the
characterisation of global minimality over $\mathbb{Q}$ by the absolute discriminant.

*Reference:*
- [Silverman2009] Joseph H. Silverman. *The Arithmetic of Elliptic Curves*. 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6),
  Proposition VII.1.3 and Section VIII.8.
-/

namespace WeierstrassCurve

section GlobalMinimal

/-- Over a number field of class number one, every Weierstrass equation has a globally minimal
model. See [Silverman2009], Corollary VIII.8.3. For zero discriminant, integrality suffices. -/
@[category textbook, AMS 11 14]
theorem exists_isGlobalMinimal {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (hK : NumberField.classNumber K = 1) :
    ∃ C : VariableChange K, (C • W).IsGlobalMinimal := by
  sorry

/-- Every Weierstrass equation over $\mathbb{Q}$ has a globally minimal model, since
$\mathbb{Q}$ has class number one. -/
@[category API, AMS 11 14]
theorem exists_isGlobalMinimal_rat (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, (C • W).IsGlobalMinimal :=
  exists_isGlobalMinimal W Rat.classNumber_eq

/-- Global minimality over $\mathbb{Q}$ is equivalent to minimising $|\Delta|$ among integral
changes of variables. See [Silverman2009], Corollary VIII.8.3 and Proposition VII.1.3.
When $\Delta = 0$, every integral model is minimal. -/
@[category textbook, AMS 11 14]
theorem isGlobalMinimal_iff_abs_Δ_le (W : WeierstrassCurve ℚ) :
    W.IsGlobalMinimal ↔ W.IsIntegral ℤ ∧
      ∀ C : VariableChange ℚ, (C • W).IsIntegral ℤ → |W.Δ| ≤ |(C • W).Δ| := by
  sorry

@[category API, AMS 11 14]
theorem IsGlobalMinimal.abs_Δ_le {W : WeierstrassCurve ℚ} [W.IsGlobalMinimal]
    (C : VariableChange ℚ) (hC : (C • W).IsIntegral ℤ) : |W.Δ| ≤ |(C • W).Δ| :=
  ((isGlobalMinimal_iff_abs_Δ_le W).1 inferInstance).2 C hC

/-- A globally minimal Weierstrass equation isomorphic to `W`, chosen using
`WeierstrassCurve.exists_isGlobalMinimal_rat`. This is the global analogue of
`WeierstrassCurve.minimal`. -/
noncomputable def globalMinimal (W : WeierstrassCurve ℚ) : WeierstrassCurve ℚ :=
  W.exists_isGlobalMinimal_rat.choose • W

instance (W : WeierstrassCurve ℚ) : W.globalMinimal.IsGlobalMinimal :=
  W.exists_isGlobalMinimal_rat.choose_spec

instance (W : WeierstrassCurve ℚ) [W.IsElliptic] : W.globalMinimal.IsElliptic :=
  inferInstanceAs (W.exists_isGlobalMinimal_rat.choose • W).IsElliptic

@[category API, AMS 11 14]
theorem exists_smul_eq_globalMinimal (W : WeierstrassCurve ℚ) :
    ∃ C : VariableChange ℚ, C • W = W.globalMinimal :=
  ⟨_, rfl⟩

@[category API, AMS 11 14]
theorem abs_Δ_eq_of_isGlobalMinimal (W : WeierstrassCurve ℚ) (C : VariableChange ℚ)
    [W.IsGlobalMinimal] [(C • W).IsGlobalMinimal] : |(C • W).Δ| = |W.Δ| := by
  have h := IsGlobalMinimal.abs_Δ_le (W := C • W) C⁻¹ (by rw [inv_smul_smul]; infer_instance)
  exact le_antisymm (by rwa [inv_smul_smul] at h) (IsGlobalMinimal.abs_Δ_le C inferInstance)

/-- Two globally minimal Weierstrass equations for the same elliptic curve over $\mathbb{Q}$ differ
by a change of variables with $u = \pm 1$. Compare [Silverman2009], Proposition VII.1.3(b). -/
@[category API, AMS 11 14]
theorem abs_u_eq_one_of_isGlobalMinimal (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : VariableChange ℚ) [W.IsGlobalMinimal] [(C • W).IsGlobalMinimal] :
    |(C.u : ℚ)| = 1 := by
  have h := abs_Δ_eq_of_isGlobalMinimal W C
  rw [variableChange_Δ, abs_mul, mul_eq_right₀ (abs_ne_zero.2 W.isUnit_Δ.ne_zero)] at h
  simpa [abs_pow, pow_eq_one_iff_of_nonneg] using h

end GlobalMinimal

end WeierstrassCurve
