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

public import FormalConjecturesUtil

/-!
# Zariski Cancellation

*References:*
- [arxiv/2208.14736](https://arxiv.org/abs/2208.14736)
  **The Zariski Cancellation Problem and related problems in Affine Algebraic Geometry**
  by *Neena Gupta*
- [OAI26a] OpenAI, *An explicit failure of complex affine-space cancellation*.
  OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/paper.pdf
-/

@[expose] public section

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

set_option linter.style.formal_proof_palomar false in
/--
The **Zariski Cancellation Problem**: is every polynomial ring over a field `k` of characteristic
`0` cancellative?

The answer is no: the polynomial ring in four variables over $\mathbb{C}$ is not cancellative.
This was disproved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof and `zariski_cancellation_problem.variants.false_complex_four`. The linked statement is
`zariski_cancellation_problem.variants.explicit`; see `zariski_cancellation_problem_of_explicit`.
-/
@[category research solved, AMS 13 14, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AffineCancellation/Main.lean#L32"]
theorem zariski_cancellation_problem :
    ¬ ∀ {k : Type} [Field k] [CharZero k] {ι : Type} [Fintype ι],
      IsCancellative k (MvPolynomial ι k) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The polynomial ring in four variables over $\mathbb{C}$ is not cancellative: there is a finitely
generated $\mathbb{C}$-domain $A$ of Krull dimension $4$ with
$A[w] \cong \mathbb{C}[x_1, \dots, x_5]$ but $A \not\cong \mathbb{C}[x_1, \dots, x_4]$.
This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean proof.
-/
@[category research solved, AMS 13 14, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AffineCancellation/Main.lean#L32"]
theorem zariski_cancellation_problem.variants.false_complex_four :
    ¬ IsCancellative ℂ (MvPolynomial (Fin 4) ℂ) := by
  sorry

/- The definitions in `ComplexCancellation` are copied from the Lean statement linked at
`zariski_cancellation_problem`. -/

namespace ComplexCancellation

noncomputable section

/-- The ambient polynomial ring $\mathbb{C}[p, s, u, F, J]$. -/
abbrev P := MvPolynomial (Fin 5) ℂ

/-- The variable `p`. -/
def p : P := MvPolynomial.X 0
/-- The variable `s`. -/
def s : P := MvPolynomial.X 1
/-- The variable `u`. -/
def u : P := MvPolynomial.X 2
/-- The variable `F`. -/
def F : P := MvPolynomial.X 3
/-- The variable `J`. -/
def J : P := MvPolynomial.X 4
/-- The polynomial $x = s^2 + u^3 + p^2 F$. -/
def x : P := s ^ 2 + u ^ 3 + p ^ 2 * F
/-- The polynomial $H = x^2 F - (1 + 2 s x) J - p^2 J^2 - p u$ that cuts out the
counterexample. -/
def H : P := x ^ 2 * F - (1 + 2 * s * x) * J - p ^ 2 * J ^ 2 - p * u
/-- The counterexample of [OAI26a]: the hypersurface algebra $\mathbb{C}[p, s, u, F, J]/(H)$. -/
abbrev A := P ⧸ Ideal.span {H}

end

end ComplexCancellation

set_option linter.style.formal_proof_palomar false in
open ComplexCancellation in
/--
The counterexample of [OAI26a], stated as in the linked Lean proof: the hypersurface algebra
`ComplexCancellation.A` is a finitely generated $\mathbb{C}$-domain of Krull dimension $4$ with
$A[w] \cong \mathbb{C}[x_1, \dots, x_5]$, but $A \not\cong \mathbb{C}[x_1, \dots, x_4]$.
-/
@[category research solved, AMS 13 14, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AffineCancellation/Main.lean#L32"]
theorem zariski_cancellation_problem.variants.explicit :
    Algebra.FiniteType ℂ A ∧ IsDomain A ∧ ringKrullDim A = 4 ∧
      Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
      ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := by
  sorry

/-- The counterexample of [OAI26a] shows that $\mathbb{C}[x_1, \dots, x_4]$ is not cancellative.
The test algebra `B` of `IsCancellative` may live in any universe, so `A` is lifted with `ULift`,
and $\mathbb{C}[x_1, \dots, x_4][w] \cong \mathbb{C}[x_1, \dots, x_5]$ is
`MvPolynomial.finSuccEquiv`. -/
@[category test, AMS 13 14]
theorem false_complex_four_of_explicit
    (h : type_of% zariski_cancellation_problem.variants.explicit) :
    type_of% zariski_cancellation_problem.variants.false_complex_four := by
  obtain ⟨hfin, -, -, ⟨e⟩, hnot⟩ := h
  intro hC
  have : Algebra.FiniteType ℂ (ULift ComplexCancellation.A) := hfin.equiv ULift.algEquiv.symm
  obtain ⟨f⟩ := hC ⟨(MvPolynomial.finSuccEquiv ℂ 4).symm.trans
    (e.symm.trans (Polynomial.mapAlgEquiv ULift.algEquiv.symm))⟩
  exact hnot ⟨(f.trans ULift.algEquiv).symm⟩

/-- The counterexample of [OAI26a] answers `zariski_cancellation_problem`. -/
@[category test, AMS 13 14]
theorem zariski_cancellation_problem_of_explicit
    (h : type_of% zariski_cancellation_problem.variants.explicit) :
    type_of% zariski_cancellation_problem :=
  fun hall => false_complex_four_of_explicit h hall

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
