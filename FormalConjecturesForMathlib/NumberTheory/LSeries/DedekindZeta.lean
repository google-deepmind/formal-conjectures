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

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind zeta function of the rationals

This file shows that on the convergence half-plane $\operatorname{Re}(s) > 1$, the Dedekind zeta
function of $\mathbb{Q}$ agrees with the Riemann zeta function.
-/

@[expose] public section

open Ideal NumberField

/-- On the convergence half-plane $\operatorname{Re}(s) > 1$, `NumberField.dedekindZeta ℚ` agrees
with `riemannZeta`. -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [NumberField.dedekindZeta, ← LSeries_one_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} _ => ?_) s
  suffices hcard : Nat.card {I : Ideal (𝓞 ℚ) // absNorm I = n} = 1 by simp [hcard]
  let φ := Rat.ringOfIntegersEquiv
  have hmap (I : Ideal (𝓞 ℚ)) : absNorm (Ideal.map φ I) = absNorm I :=
    Nat.card_congr (Ideal.quotientEquiv I _ φ rfl).toEquiv.symm
  have hsurj (J : Ideal ℤ) : Ideal.map φ (Ideal.comap φ J) = J :=
    Ideal.map_comap_of_surjective _ φ.surjective J
  let e : {I : Ideal (𝓞 ℚ) // absNorm I = n} ≃ {J : Ideal ℤ // absNorm J = n} :=
    ⟨fun ⟨I, hI⟩ => ⟨Ideal.map φ I, (hmap I).trans hI⟩,
      fun ⟨J, hJ⟩ => ⟨Ideal.comap φ J, by rw [← hmap, hsurj, hJ]⟩,
      fun ⟨I, _⟩ => Subtype.ext <| Ideal.comap_map_of_bijective _ φ.bijective,
      fun ⟨J, _⟩ => Subtype.ext <| hsurj J⟩
  rw [Nat.card_congr e]
  let : Unique {J : Ideal ℤ // absNorm J = n} :=
    { default := ⟨Ideal.span {(n : ℤ)}, by simp⟩
      uniq := fun ⟨J, hJ⟩ => Subtype.ext <| by
        dsimp only; rw [← hJ, Int.ideal_span_absNorm_eq_self] }
  exact Nat.card_unique
