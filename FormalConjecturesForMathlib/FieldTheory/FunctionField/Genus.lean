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

public import FormalConjecturesForMathlib.FieldTheory.FunctionField.Place

/-!
# Divisors, Riemann-Roch spaces and the genus

This file defines the divisors of a field extension `F / K`, their degrees, their Riemann-Roch
spaces $L(D)$, and the genus of `F / K`. The genus is the least $g$ for which Riemann's inequality
$\ell(D) \geq \deg D + 1 - g$ holds for every divisor $D$.

These definitions are meant for function fields of one variable. On other extensions they can
return junk values; see the docstring of `FunctionField.genus`.

## References

- Henning Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer GTM 254,
  Section 1.4, https://doi.org/10.1007/978-3-540-76878-4
-/

@[expose] public section

namespace FunctionField

open Module (finrank)
open WithZero (exp)

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A divisor of $F / K$: a finitely supported formal `ℤ`-linear combination of places. -/
abbrev Divisor : Type _ := Place K F →₀ ℤ

variable {K F}

/-- The degree $\sum_P n_P \deg P$ of a divisor. -/
noncomputable def Divisor.degree (D : Divisor K F) : ℤ := D.sum fun P n => n * P.degree

/-- The Riemann-Roch space
$L(D) = \{f \in F \mid \operatorname{ord}_P(f) \geq -D(P) \text{ for every place } P\}$ of a
divisor `D`. In the multiplicative convention $v_P = \exp(-\operatorname{ord}_P)$ the condition
reads $v_P(f) \leq \exp(D(P))$. -/
def riemannRochSpace (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ P : Place K F, P.v f ≤ exp (D P)}
  add_mem' hf hg P := P.v.map_add_le (hf P) (hg P)
  zero_mem' P := by simp
  smul_mem' a f hf P := by
    rw [Algebra.smul_def, map_mul]
    exact le_trans (mul_le_of_le_one_left'
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one P.v a)) (hf P)

/-- Membership in a Riemann-Roch space, unfolded. -/
theorem mem_riemannRochSpace {D : Divisor K F} {f : F} :
    f ∈ riemannRochSpace D ↔ ∀ P : Place K F, P.v f ≤ exp (D P) := Iff.rfl

/-- `L(0)` contains the constants, because a constant function has no poles. -/
theorem algebraMap_mem_riemannRochSpace_zero (a : K) :
    algebraMap K F a ∈ riemannRochSpace (0 : Divisor K F) := fun P => by
  simp

/-- Allowing more poles gives a bigger Riemann-Roch space. This fixes the sign convention: with
`D` and `-D` exchanged the Riemann-Roch space would be antitone instead. -/
theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := fun _ hf P =>
  (hf P).trans (WithZero.exp_le_exp.2 (h P))

variable (K F)

/-- The genus of $F / K$: the least `g` for which Riemann's inequality
$\ell(D) \geq \deg D + 1 - g$ holds for every divisor `D`. Equivalently
$g = \max_D (\deg D - \ell(D) + 1)$, which is Stichtenoth's definition.

This is the usual genus only for a function field of one variable. On an arbitrary extension it
returns the junk value `sInf ∅ = 0` whenever no `g` satisfies the inequality. This would also
happen if the Riemann-Roch spaces were infinite-dimensional, since `finrank` is `0` on those.
Riemann's inequality for function fields of one variable rules this out; it is not proved here. -/
noncomputable def genus : ℕ :=
  sInf {g : ℕ | ∀ D : Divisor K F,
    D.degree + 1 - (g : ℤ) ≤ (finrank K (riemannRochSpace D) : ℤ)}

/-- A trivial extension has genus `0`: it has no places, so its only divisor is `0`, and
`L(0) = K`. This exercises `genus` through divisors, degrees and Riemann-Roch spaces. It does not
by itself distinguish `genus` from the junk value `sInf ∅ = 0`. -/
theorem genus_self : genus K K = 0 := by
  have hempty := isEmpty_place_self K
  refine Nat.sInf_eq_zero.2 (Or.inl fun D => ?_)
  have h1 : D.degree = 0 := by
    rw [Divisor.degree, Finsupp.sum, Finset.eq_empty_of_isEmpty D.support, Finset.sum_empty]
  have h2 : riemannRochSpace D = ⊤ := by
    ext f
    simp only [mem_riemannRochSpace, Submodule.mem_top, iff_true]
    exact fun P => hempty.elim P
  rw [h1, h2]
  simp

end FunctionField
