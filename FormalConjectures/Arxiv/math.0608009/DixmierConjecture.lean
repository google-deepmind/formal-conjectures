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
import FormalConjectures.Arxiv.«math.0608009».PoissonConjecture

/-!
# The Dixmier Conjecture

*References:*
- [Dix68] [Sur les algèbres de Weyl](http://www.numdam.org/item/BSMF_1968__96__209_0/)
  by *Jacques Dixmier*, Bull. Soc. Math. France 96 (1968), 209–242. The conjecture is
  Problem 1 (for the first Weyl algebra).
- [BCW82] [The Jacobian conjecture: reduction of degree and formal expansion of the inverse](https://doi.org/10.1090/S0273-0979-1982-15032-7)
  by *Hyman Bass, Edwin H. Connell, David Wright*, Bull. Amer. Math. Soc. 7 (1982),
  287–330. Proves `DC_n ⟹ JC_n`.
- [AvdE07] [arxiv/math.0608009](https://arxiv.org/abs/math/0608009)
  **On the equivalence of the Jacobian, Dixmier and Poisson Conjectures in any characteristic**
  by *Kossivi Adjamagbo, Arno van den Essen*. Published as *A proof of the equivalence of
  the Dixmier, Jacobian and Poisson conjectures*, Acta Math. Vietnam. 32 (2007), 205–214.
- [Tsu05] [Endomorphisms of Weyl algebra and p-curvatures](https://projecteuclid.org/euclid.ojm/1153494380)
  by *Yoshifumi Tsuchimoto*, Osaka J. Math. 42 (2005), 435–452. Proves the stable
  equivalence `JC ⟺ DC` independently.
- [BKK07] [The Jacobian Conjecture is stably equivalent to the Dixmier Conjecture](https://doi.org/10.17323/1609-4514-2007-7-2-209-218)
  by *Alexei Belov-Kanel, Maxim Kontsevich*, Moscow Math. J. 7 (2007), 209–218. Independent
  proof of the stable equivalence.
- [Bav20] [The Jacobian Conjecture implies the Dixmier Problem](https://arxiv.org/abs/math/0512250)
  by *Vladimir Bavula*; published in Springer Proceedings in Mathematics & Statistics 317
  (2020). A third proof.
- [Alp26] [Counterexample to the Jacobian conjecture](https://x.com/__alpoge__/status/2079028340955197566)
  by *Levent Alpöge* (2026), disproving the Jacobian conjecture in dimension 3; formalised
  against this repository's statement in
  [PR #4474](https://github.com/google-deepmind/formal-conjectures/pull/4474).

The Dixmier Conjecture `DC_n` asserts that, over a field `K` of characteristic zero, every
endomorphism of the `n`-th Weyl algebra $A_n(K)$ is an automorphism. For `n = 1` this is
Problem 1 of [Dix68] and remains open; it is the weakest link of the surviving chain of
implications (see below).

By [BCW82], `DC_n ⟹ JC_n` (the Jacobian conjecture in dimension `n`), and by [AvdE07],
Theorem 7, the full chain $JC_{2n} ⟹ PC_n ⟹ DC_n ⟹ JC_n$ holds per dimension.
Since the Jacobian conjecture fails in every dimension `n ≥ 3` [Alp26], the contrapositive
of [BCW82] gives that `DC_n` is **false for all n ≥ 3**, while `DC_1` and `DC_2` remain
open, sitting in the surviving totally ordered chain
$PC_2 ⟹ DC_2 ⟹ JC_2 ⟹ PC_1 ⟹ DC_1$.

The Weyl algebra $A_n(K)$ is `WeylAlgebra K (Fin n)`, with the `2n` generators indexed by
`Fin n ⊕ Fin n` as in `FormalConjecturesForMathlib/Algebra/WeylAlgebra.lean`; the Poisson
side of the chain is stated in `PoissonConjecture.lean` in this directory.
-/

namespace Arxiv.«math.0608009»

variable {K : Type*} [Field K] [CharZero K]

variable (K) in
/-- The Dixmier Conjecture in dimension `n` (`DC_n`): every endomorphism of the `n`-th
Weyl algebra over `K` (a field of characteristic zero) is an automorphism. An algebra
endomorphism is an automorphism iff it is bijective. -/
def DixmierConjectureFor (n : ℕ) : Prop :=
  ∀ φ : WeylAlgebra K (Fin n) →ₐ[K] WeylAlgebra K (Fin n), Function.Bijective φ

/--
The **Dixmier Conjecture** (generalised to all dimensions; Problem 1 of [Dix68] for
`n = 1`): for every `n`, every endomorphism of the `n`-th Weyl algebra over a field of
characteristic zero is an automorphism. This is **false**: the Jacobian conjecture fails
in dimension 3 [Alp26], and `DC_n ⟹ JC_n` [BCW82], so `DC_3` fails.
-/
@[category research solved, AMS 16]
theorem dixmier_conjecture : ¬ ∀ n, DixmierConjectureFor K n := by
  sorry

/--
The Dixmier Conjecture in dimension 1 — Problem 1 of [Dix68] — is open. It is the weakest
link of the surviving chain $PC_2 ⟹ DC_2 ⟹ JC_2 ⟹ PC_1 ⟹ DC_1$ ([AvdE07],
Theorem 7): every other open conjecture in the family implies it.
-/
@[category research open, AMS 16]
theorem dixmier_conjecture.variants.dimension_one : DixmierConjectureFor K 1 := by
  sorry

/--
The Dixmier Conjecture in dimension 2 (`DC_2`) is open. It is implied by `PC_2` and
implies Keller's original two-variable Jacobian conjecture `JC_2` ([AvdE07], Theorem 7;
[BCW82]).
-/
@[category research open, AMS 16]
theorem dixmier_conjecture.variants.dimension_two : DixmierConjectureFor K 2 := by
  sorry

/--
The Dixmier Conjecture is false in dimension 3: `DC_3` implies the Jacobian conjecture in
dimension 3 [BCW82], which fails by the counterexample of [Alp26].
-/
@[category research solved, AMS 16]
theorem dixmier_conjecture.variants.dimension_three : ¬ DixmierConjectureFor K 3 := by
  sorry

/--
The Dixmier Conjecture is false in every dimension `n ≥ 3`, since the Jacobian conjecture
is false in every dimension `n ≥ 3` (padding the counterexample of [Alp26] with identity
coordinates) and `DC_n ⟹ JC_n` [BCW82].
-/
@[category research solved, AMS 16]
theorem dixmier_conjecture.variants.dimension_ge_three (n : ℕ) (hn : 3 ≤ n) :
    ¬ DixmierConjectureFor K n := by
  sorry

/--
The Dixmier conjecture in dimension `n` implies the Jacobian conjecture in dimension `n`
([BCW82]; see also [AvdE07], Theorem 7).
-/
@[category research solved, AMS 14 16]
theorem dixmier_conjecture.variants.jacobian_implication (n : ℕ)
    (h : DixmierConjectureFor K n) : JacobianConjectureFor K n := by
  sorry

/--
The Poisson conjecture in dimension `n` implies the Dixmier conjecture in dimension `n`
([AvdE07], Theorem 7; the proof passes through reduction to prime characteristic and the
Azumaya property of Weyl algebras in characteristic `p`).
-/
@[category research solved, AMS 14 16 17]
theorem dixmier_conjecture.variants.poisson_implication (n : ℕ)
    (h : PoissonConjectureFor K n) : DixmierConjectureFor K n := by
  sorry

section Tests

omit [CharZero K] in
/-- The canonical commutation relation `[Yᵢ, Y_{i+n}] = 1` holds in the Weyl algebra. -/
@[category test, AMS 16]
theorem weylAlgebra_commutator (n : ℕ) (i : Fin n) :
    WeylAlgebra.of K (Sum.inl i) * WeylAlgebra.of K (Sum.inr i) -
      WeylAlgebra.of K (Sum.inr i) * WeylAlgebra.of K (Sum.inl i) = 1 :=
  WeylAlgebra.commutator_of_inl_of_inr_self K i

end Tests

end Arxiv.«math.0608009»
