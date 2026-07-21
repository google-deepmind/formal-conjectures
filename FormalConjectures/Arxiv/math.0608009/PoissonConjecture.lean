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
import FormalConjectures.Wikipedia.JacobianConjecture

/-!
# The Poisson Conjecture

*References:*
- [AvdE07] [arxiv/math.0608009](https://arxiv.org/abs/math/0608009)
  **On the equivalence of the Jacobian, Dixmier and Poisson Conjectures in any characteristic**
  by *Kossivi Adjamagbo, Arno van den Essen*. Published as *A proof of the equivalence of the
  Dixmier, Jacobian and Poisson conjectures*, Acta Math. Vietnam. 32 (2007), 205–214.
- [BCW82] [The Jacobian conjecture: reduction of degree and formal expansion of the inverse](https://doi.org/10.1090/S0273-0979-1982-15032-7)
  by *Hyman Bass, Edwin H. Connell, David Wright*, Bull. Amer. Math. Soc. 7 (1982), 287–330.
- [Alp26] [Counterexample to the Jacobian conjecture](https://x.com/__alpoge__/status/2079028340955197566)
  by *Levent Alpöge* (2026), disproving the Jacobian conjecture in dimension 3; formalised
  against this repository's statement in
  [PR #4474](https://github.com/google-deepmind/formal-conjectures/pull/4474).

The Poisson Conjecture `PC_n` ([AvdE07], Notations 5) asserts that, over a field of
characteristic zero, every endomorphism of the `n`-th canonical Poisson algebra
$P_n(K)$ — the polynomial algebra $K[X_1, \dots, X_{2n}]$ equipped with the canonical
Poisson bracket — is an automorphism.

By [AvdE07], Theorem 7 (the "United Conjectures Theorem"), for every `n` there is a chain
of implications
$$JC_{2n} \Longrightarrow PC_n \Longrightarrow DC_n \Longrightarrow JC_n,$$
where `JC_n` is the Jacobian Conjecture in dimension `n` and `DC_n` the Dixmier Conjecture
for the `n`-th Weyl algebra (the implication `DC_n ⟹ JC_n` being classical [BCW82]).
Since the Jacobian conjecture was disproved in dimension 3 [Alp26] — and hence in every
dimension `n ≥ 3` by padding with identity coordinates — `PC_n` is false for all `n ≥ 3`:
composing the counterexample's failure of `JC_3` through `PC_3 ⟹ DC_3 ⟹ JC_3` refutes
`PC_3`, and directly, the cotangent (symplectic) lift of the counterexample map
([AvdE07], Theorem 1 in reverse) is a non-invertible Poisson endomorphism of $P_3(K)$.
The cases `n = 1` and `n = 2` remain open.

Indexing note: we index the `2n` variables of $P_n(K)$ by `Fin n ⊕ Fin n`, with
`Sum.inl i` playing the role of $X_i$ and `Sum.inr i` the role of $X_{i+n}$ of [AvdE07],
so that the canonical bracket reads $\{X_i, X_{i+n}\} = 1$; see
`MvPolynomial.poissonBracket`.
-/

namespace Arxiv.«math.0608009»

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A `K`-algebra endomorphism `φ` of the polynomial algebra in `2n` variables is an
endomorphism of the `n`-th canonical Poisson algebra $P_n(K)$ if it preserves the canonical
Poisson bracket. Following [AvdE07], Lemma 2, it is equivalent to require preservation on
the generators only, which is the form used here (the brackets of generators are constants,
so preserving and intertwining them agree). -/
def IsPoissonEndomorphism {n : ℕ}
    (φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K) : Prop :=
  ∀ v w, poissonBracket (φ (X v)) (φ (X w)) = poissonBracket (X v) (X w)

variable (K) in
/-- The Poisson Conjecture in dimension `n` (`PC_n` in the notation of [AvdE07]): every
endomorphism of the `n`-th canonical Poisson algebra over `K` is an automorphism.
An endomorphism is an automorphism iff it is bijective, since the inverse of a bijective
algebra endomorphism preserving the Poisson bracket is again such. -/
def PoissonConjectureFor (n : ℕ) : Prop :=
  ∀ φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K,
    IsPoissonEndomorphism φ → Function.Bijective φ

variable (K) in
/-- The Jacobian Conjecture in dimension `m`, the per-dimension form of
`JacobianConjecture.jacobian_conjecture`: every polynomial endomorphism of $K^m$ with unit
Jacobian determinant has a polynomial inverse. -/
def JacobianConjectureFor (m : ℕ) : Prop :=
  ∀ F : JacobianConjecture.RegularFunction K (Fin m) (Fin m), IsUnit F.Jacobian.det →
    ∃ G : JacobianConjecture.RegularFunction K (Fin m) (Fin m),
      G.comp F = JacobianConjecture.RegularFunction.id K (Fin m) ∧
      F.comp G = JacobianConjecture.RegularFunction.id K (Fin m)

/--
The **Poisson Conjecture** ([AvdE07], the characteristic zero case): for every `n`, every
endomorphism of the `n`-th canonical Poisson algebra over a field `K` of characteristic
zero is an automorphism. This is **false**: the Jacobian conjecture fails in dimension 3
[Alp26], hence so does `PC_3` (via [AvdE07], Theorem 7, or directly via the symplectic
lift of the counterexample map).
-/
@[category research solved, AMS 14 17]
theorem poisson_conjecture : ¬ ∀ n, PoissonConjectureFor K n := by
  sorry

/--
The Poisson Conjecture in dimension 1 (`PC_1`) is open. By [AvdE07], Theorem 7, it is
implied by the Jacobian conjecture in dimension 2 (Keller's original problem, open) and
implies the Dixmier conjecture for the first Weyl algebra (Problem 1 of Dixmier (1968),
open).
-/
@[category research open, AMS 14 17]
theorem poisson_conjecture.variants.dimension_one : PoissonConjectureFor K 1 := by
  sorry

/--
The Poisson Conjecture in dimension 2 (`PC_2`) is open. Since the Jacobian conjecture is
false in every dimension `n ≥ 3` [Alp26], no known implication bounds `PC_2` from above
any more; the chain of [AvdE07], Theorem 7 places it as the strongest of the remaining
open conjectures $PC_2 ⟹ DC_2 ⟹ JC_2 ⟹ PC_1 ⟹ DC_1$.
-/
@[category research open, AMS 14 17]
theorem poisson_conjecture.variants.dimension_two : PoissonConjectureFor K 2 := by
  sorry

/--
The Poisson Conjecture is false in dimension 3: the cotangent (symplectic) lift
$\Phi(X_i) = F_i$, $\Phi(X_{i+3}) = \sum_j M_{ij} X_{j+3}$ with $M = (JF)^{-\top}$ of the
degree-6 counterexample map $F$ of [Alp26] (whose Jacobian determinant is the constant
$-2$, so $M$ is a polynomial matrix) is a Poisson endomorphism of $P_3(K)$ that is not
injective on points — e.g. it identifies $(0, 6, -142, 0, 0, 0)$ and $(1, 0, 2, 0, 0, 0)$
— and is therefore no automorphism. Alternatively, `PC_3` fails by [AvdE07], Theorem 7,
as it implies the Jacobian conjecture in dimension 3, contradicting [Alp26].
-/
@[category research solved, AMS 14 17]
theorem poisson_conjecture.variants.dimension_three : ¬ PoissonConjectureFor K 3 := by
  sorry

/--
The Poisson Conjecture is false in every dimension `n ≥ 3`, by padding the dimension 3
counterexample with identity coordinates.
-/
@[category research solved, AMS 14 17]
theorem poisson_conjecture.variants.dimension_ge_three (n : ℕ) (hn : 3 ≤ n) :
    ¬ PoissonConjectureFor K n := by
  sorry

/--
The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`
([AvdE07], Theorem 1 and Theorem 7).
-/
@[category research solved, AMS 14 17]
theorem poisson_conjecture.variants.jacobian_implication (n : ℕ)
    (h : JacobianConjectureFor K (2 * n)) : PoissonConjectureFor K n := by
  sorry

section Tests

omit [CharZero K] in
/-- The identity is a Poisson endomorphism. -/
@[category test, AMS 17]
theorem isPoissonEndomorphism_id (n : ℕ) :
    IsPoissonEndomorphism (AlgHom.id K (MvPolynomial (Fin n ⊕ Fin n) K)) := by
  intro v w
  simp

omit [CharZero K] in
/-- The canonical bracket pairs each position variable with its momentum variable. -/
@[category test, AMS 17]
theorem poissonBracket_X_pairing (n : ℕ) (i : Fin n) :
    poissonBracket (X (Sum.inl i) : MvPolynomial (Fin n ⊕ Fin n) K) (X (Sum.inr i)) = 1 := by
  simp

omit [CharZero K] in
/-- The Poisson conjecture holds trivially in dimension 0, where the Poisson algebra is `K`
itself and the identity is the only endomorphism. -/
@[category test, AMS 17]
theorem poissonConjectureFor_zero : PoissonConjectureFor K 0 := by
  intro φ _
  have : φ = AlgHom.id K _ := algHom_ext fun i => i.elim (fun h => h.elim0) fun h => h.elim0
  rw [this]
  exact Function.bijective_id

end Tests

end Arxiv.«math.0608009»
