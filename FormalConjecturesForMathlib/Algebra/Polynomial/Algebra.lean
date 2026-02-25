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

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Algebraic.Pi

/-!
# Algebra over the Ring of Polynomials

-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Polynomial

instance instAlgebraPi : Algebra R[X] (S → S) :=
  (Pi.ringHom fun x ↦ (Polynomial.aeval x).toRingHom).toAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- #TODO:  Generalize the following lemma to `CommSemiring`. -/
@[simp] lemma aeval_polynomial_pi (p : R[X][X]) (f : S → S) (x : S) :
    p.aeval f x = aevalAeval x (f x) p := by
  simp [instAlgebraPi, aeval, eval₂, sum]

end Polynomial
