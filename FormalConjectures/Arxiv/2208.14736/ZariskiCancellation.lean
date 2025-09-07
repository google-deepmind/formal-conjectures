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

import FormalConjectures.Util.ProblemImports

/-!
# Zariski Cancellation

*Reference:* [arxiv/2208.14736](https://arxiv.org/abs/2208.14736)
**The Zariski Cancellation Problem and related problems in Affine Algebraic Geometry**
by *Neena Gupta*
-/

namespace Arxiv.«2208.14736»

open Polynomial

/--
A finitely generated `k`-algebra `A` is cancellative if for all finitely generated `k` algebras `B` such that
`B[X] ≅ₖ A[X]` we have `B ≅ₖ A`.
-/
def IsCancellative (k A : Type*) [Field k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] : Prop := ∀ {B : Type*}
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B], Nonempty (A[X] ≃ₐ[k] B[X]) →
    Nonempty (A ≃ₐ[k] B)

/--
The **Zariski Cancellation Problem**: every polynomial ring over a field `k` of characteristic
`0` is cancellative.
-/
@[category research open, AMS 13 14]
theorem zariski_cancellation_problem {k : Type*} [Field k]
    [CharZero k] {ι : Type*} [Fintype ι] : IsCancellative k (MvPolynomial ι k) := by
  sorry

/--
The single variable polynomial ring `k[X]` is cancellative in any characteristic
-/
@[category research solved, AMS 13 14]
theorem zariski_cancellation_problem.variants.dim_one
    {k : Type*} [Field k] : IsCancellative k k[X] := by
  sorry

/--
The two variable polynomial ring `k[X]` is cancellative in any characteristic
-/
@[category research solved, AMS 13 14]
theorem zariski_cancellation_problem.variants.dim_two {k : Type*} [Field k] :
    IsCancellative k (MvPolynomial (Fin 2) k) := by
  sorry

/--
The positive characteristic case of the Zariski Cancellation Problem is false in dimension `3`
-/
@[category research solved, AMS 13 14]
theorem zariski_cancellation_problem.variants.false_pos_card
    (p : ℕ) [hp : Fact p.Prime] {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) :
    ¬ IsCancellative (ZMod p) (MvPolynomial ι (ZMod p)) := by
  sorry

end Arxiv.«2208.14736»
