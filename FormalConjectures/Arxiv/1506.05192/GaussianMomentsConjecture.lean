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
# The Gaussian Moments Conjecture in Dimension Two

*Conjecture reference:* [Derksen, van den Essen, and Zhao,
The Gaussian Moments Conjecture and the Jacobian
Conjecture](https://arxiv.org/abs/1506.05192)

*Proof reference:* [Proof announcement](https://x.com/swe_acc/status/2079881074826420446)
-/

open MeasureTheory ProbabilityTheory

namespace GaussianMomentsConjecture

abbrev Polynomial2 := MvPolynomial (Fin 2) ℂ

noncomputable def polynomialEval (P : Polynomial2) (p : ℝ × ℝ) : ℂ :=
  MvPolynomial.eval₂ (RingHom.id ℂ)
    (fun i => if i = (0 : Fin 2) then (p.1 : ℂ) else (p.2 : ℂ)) P

noncomputable def gaussianExpectation (P : Polynomial2) : ℂ :=
  ∫ p : ℝ × ℝ, polynomialEval P p
    ∂(gaussianReal 0 1).prod (gaussianReal 0 1)

def AllMomentsZero (P : Polynomial2) : Prop :=
  ∀ m : ℕ, 1 ≤ m → gaussianExpectation (P ^ m) = 0

def EventuallyMixedZero (Q P : Polynomial2) : Prop :=
  ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
    gaussianExpectation (Q * P ^ m) = 0

/--
The Gaussian Moments Conjecture of Derksen, van den Essen, and Zhao,
specialized to two independent standard real Gaussian variables.
-/
@[category research solved, AMS 14 33 60,
  formal_proof using lean4 at
    "https://github.com/MurrellGroup/GMC-2-lean/blob/1fc9242372915ee48a3a989cacf3c27675923b3b/GMC2/RealGaussian.lean#L743"]
theorem gaussianMomentsConjectureTwo :
    ∀ P : Polynomial2, AllMomentsZero P →
      ∀ Q : Polynomial2, EventuallyMixedZero Q P := by
  sorry

end GaussianMomentsConjecture
