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
# Complete disjoint NP pairs

*References:*
* [Ra94] Razborov, A. A. (1994). "On provably disjoint NP-pairs." *BRICS Report Series*
  RS-94-36; ECCC TR94-006.
* [KMT03] Köbler, J., Messner, J., and Torán, J. (2003). "Optimal proof systems imply complete
  sets for promise classes." *Inform. and Comput.* 184, pp. 71--92.
* [GSSZ04] Glaßer, C., Selman, A. L., Sengupta, S., and Zhang, L. (2004). "Disjoint NP-pairs."
  *SIAM J. Comput.* 33, pp. 1369--1416.
* [Pu17] Pudlák, P. (2017). "Incompleteness in the finite domain." *Bull. Symbolic Logic* 23,
  pp. 405--441. [arXiv:1601.01487](https://arxiv.org/abs/1601.01487)
* [Kh22] Khaniki, E. (2022). "New relations and separations of conjectures about incompleteness
  in the finite domain." *J. Symbolic Logic* 87, pp. 912--937.
  [arXiv:1904.01362](https://arxiv.org/abs/1904.01362)
-/

namespace DisjointNPPairs

open ComplexityTheory

/-- A **disjoint NP pair**: two languages in `NP` with no common element. -/
structure IsDisjointNPPair (A B : DecisionProblem) : Prop where
  memA : A ∈ NP
  memB : B ∈ NP
  disjoint : ∀ x, ¬(A x = true ∧ B x = true)

/-- A **disjoint coNP pair**: two languages in `coNP` with no common element. -/
structure IsDisjointCoNPPair (A B : DecisionProblem) : Prop where
  memA : A ∈ coNP
  memB : B ∈ coNP
  disjoint : ∀ x, ¬(A x = true ∧ B x = true)

/-- The pair `(A, B)` **reduces** to the pair `(A', B')`: a polynomial-time map sends `A` into
`A'` and `B` into `B'` (a many-one reduction of pairs, [GSSZ04, Definition 3.1]). -/
def PairReducible (A B A' B' : DecisionProblem) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧
    (∀ x, A x = true → A' (f x) = true) ∧ (∀ x, B x = true → B' (f x) = true)

/-- `(A, B)` is a **complete disjoint NP pair**: a disjoint NP pair to which every disjoint NP
pair reduces. -/
def IsCompleteNPPair (A B : DecisionProblem) : Prop :=
  IsDisjointNPPair A B ∧ ∀ A' B', IsDisjointNPPair A' B' → PairReducible A' B' A B

/-- `(A, B)` is a **complete disjoint coNP pair**. -/
def IsCompleteCoNPPair (A B : DecisionProblem) : Prop :=
  IsDisjointCoNPPair A B ∧ ∀ A' B', IsDisjointCoNPPair A' B' → PairReducible A' B' A B

/-- A pair `(A, B)` is **P-separable** if some language in `P` contains `A` and misses `B`. -/
def IsPSeparable (A B : DecisionProblem) : Prop :=
  ∃ S ∈ P, (∀ x, A x = true → S x = true) ∧ ∀ x, B x = true → S x = false

/-- Every pair reduces to itself. -/
@[category API, AMS 3 68]
lemma pairReducible_refl (A B : DecisionProblem) : PairReducible A B A B :=
  ⟨id, isPolyTime_id, fun _ h => h, fun _ h => h⟩

/-- Disjointness of NP pairs is symmetric. -/
@[category API, AMS 3 68]
lemma IsDisjointNPPair.symm {A B : DecisionProblem} (h : IsDisjointNPPair A B) :
    IsDisjointNPPair B A :=
  ⟨h.memB, h.memA, fun x hx => h.disjoint x ⟨hx.2, hx.1⟩⟩

/-- Disjointness of coNP pairs is symmetric. -/
@[category API, AMS 3 68]
lemma IsDisjointCoNPPair.symm {A B : DecisionProblem} (h : IsDisjointCoNPPair A B) :
    IsDisjointCoNPPair B A :=
  ⟨h.memB, h.memA, fun x hx => h.disjoint x ⟨hx.2, hx.1⟩⟩

/-- A P-separable pair is disjoint. -/
@[category API, AMS 3 68]
lemma IsPSeparable.disjoint {A B : DecisionProblem} (h : IsPSeparable A B) (x : List Bool) :
    ¬(A x = true ∧ B x = true) := by
  obtain ⟨S, -, hA, hB⟩ := h
  rintro ⟨ha, hb⟩
  have h1 := hA x ha
  have h2 := hB x hb
  rw [h1] at h2
  cases h2

/--
**There is no complete disjoint NP pair** (Razborov [Ra94]; Pudlák's conjecture `DisjNP` [Pu17]).

No disjoint NP pair is complete under polynomial-time many-one reductions of pairs. This is the
strongest of the "incompleteness in the finite domain" conjectures: it implies that no
length-optimal propositional proof system exists [Ra94, KMT03], hence `NP ≠ coNP` and `P ≠ NP`.
Equivalently [Pu17], for every consistent polynomial-time axiomatized theory `T ⊇ S¹₂` some
disjoint NP pair is not provably disjoint in `T`.
-/
@[category research open, AMS 3 68]
theorem no_complete_disjoint_NP_pair : ¬∃ A B : DecisionProblem, IsCompleteNPPair A B := by
  sorry

/--
**There is no complete disjoint coNP pair** (Pudlák's conjecture `DisjCoNP` [Pu17]).

No disjoint coNP pair is complete under polynomial-time many-one reductions of pairs. This
implies that `TFNP` has no complete problem and that `SAT` has no p-optimal proof system
[Pu17, Kh22].
-/
@[category research open, AMS 3 68]
theorem no_complete_disjoint_coNP_pair : ¬∃ A B : DecisionProblem, IsCompleteCoNPPair A B := by
  sorry

/--
**If `NP = coNP` then a complete disjoint NP pair exists** [GSSZ04, Pu17].

The pair `(SAT, ¬SAT)` is then a disjoint NP pair, and every disjoint NP pair `(A, B)` reduces
to it via a Cook–Levin reduction of `A` to `SAT`, since `B` is disjoint from `A`.
-/
@[category research solved, AMS 3 68]
theorem no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP (h : NP = coNP) :
    ∃ A B : DecisionProblem, IsCompleteNPPair A B := by
  sorry

/--
**The conjecture implies `NP ≠ coNP`** [Pu17].
-/
@[category research solved, AMS 3 68]
theorem no_complete_disjoint_NP_pair.variants.NP_ne_coNP
    (h : ¬∃ A B : DecisionProblem, IsCompleteNPPair A B) : NP ≠ coNP :=
  fun heq => h (no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP heq)

/--
**If `P = NP` then every disjoint NP pair is P-separable**, and hence a complete pair exists:
each `A` is then in `P` and separates `(A, B)`.
-/
@[category textbook, AMS 3 68]
theorem no_complete_disjoint_NP_pair.variants.pSeparable_of_P_eq_NP (h : P = NP)
    {A B : DecisionProblem} (hAB : IsDisjointNPPair A B) : IsPSeparable A B := by
  refine ⟨A, by rw [h]; exact hAB.memA, fun _ hx => hx, fun x hx => ?_⟩
  have := hAB.disjoint x
  cases hA : A x
  · rfl
  · exact absurd ⟨hA, hx⟩ this

end DisjointNPPairs
