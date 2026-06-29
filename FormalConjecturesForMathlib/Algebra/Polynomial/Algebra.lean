/-
Copyright 2025 The Formal Conjectures Authors.

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


public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Algebraic.Pi

@[expose] public noncomputable section

/-!
# Algebra over the Ring of Polynomials

-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Polynomial

instance instAlgebraPi : Algebra R[X] (S → S) :=
  (Pi.ringHom fun s ↦ (Polynomial.aeval s).toRingHom).toAlgebra

@[simp]
lemma algebraMap_algebraPi (p : R[X]) (s : S) : algebraMap R[X] (S → S) p s = aeval s p := rfl

@[simp] lemma aeval_polynomial_pi (p : R[X][X]) (f : S → S) (x : S) :
    p.aeval f x = aevalAeval x (f x) p := by
  induction p using Polynomial.induction_on' with
  | add => simp [*]
  | monomial n q =>
  simp only [aeval_monomial, Pi.mul_apply, Pi.pow_apply, aevalAevalEquiv_apply_apply,
    algebraMap_def, coe_mapRingHom, eval_mul, eval_map_algebraMap, eval_pow, eval_C]
  induction q using Polynomial.induction_on' with
  | add => simp [add_mul, *]
  | monomial n p => simp

end Polynomial
