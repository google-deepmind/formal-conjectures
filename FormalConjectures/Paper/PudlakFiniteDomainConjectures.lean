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
# Pudlák's conjectures on incompleteness in the finite domain

*References:*
* [CR79] Cook, S. A. and Reckhow, R. A. (1979). "The relative efficiency of propositional proof
  systems." *J. Symbolic Logic* 44, pp. 36--50.
* [HH88] Hartmanis, J. and Hemachandra, L. A. (1988). "Complexity classes without machines: on
  complete languages for UP." *Theoret. Comput. Sci.* 58, pp. 129--142.
* [KP89] Krajíček, J. and Pudlák, P. (1989). "Propositional proof systems, the consistency of
  first order theories and the complexity of computations." *J. Symbolic Logic* 54,
  pp. 1063--1079.
* [MP91] Megiddo, N. and Papadimitriou, C. H. (1991). "On total functions, existence theorems
  and computational complexity." *Theoret. Comput. Sci.* 81, pp. 317--324.
* [Pa94] Papadimitriou, C. H. (1994). "On the complexity of the parity argument and other
  inefficient proofs of existence." *J. Comput. System Sci.* 48, pp. 498--532.
* [KMT03] Köbler, J., Messner, J., and Torán, J. (2003). "Optimal proof systems imply complete
  sets for promise classes." *Inform. and Comput.* 184, pp. 71--92.
* [Pu17] Pudlák, P. (2017). "Incompleteness in the finite domain." *Bull. Symbolic Logic* 23,
  pp. 405--441. [arXiv:1601.01487](https://arxiv.org/abs/1601.01487)
* [Kh22] Khaniki, E. (2022). "New relations and separations of conjectures about incompleteness
  in the finite domain." *J. Symbolic Logic* 87, pp. 912--937.
  [arXiv:1904.01362](https://arxiv.org/abs/1904.01362)
-/

namespace PudlakFiniteDomain

open ComplexityTheory

/-- `A` **many-one reduces** to `B` in polynomial time. -/
def ManyOneReducible (A B : DecisionProblem) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧ ∀ x, A x = B (f x)

/-- `L` is **complete** for the class `C` under polynomial-time many-one reductions. -/
def IsCompleteFor (C : DecisionComplexityClass) (L : DecisionProblem) : Prop :=
  L ∈ C ∧ ∀ L' ∈ C, ManyOneReducible L' L

/-- The class **UP**: languages accepted by a polynomial-time verifier with at most one
witness per input. -/
def UP : DecisionComplexityClass :=
  { L | ∃ (p : Polynomial ℕ) (R : List Bool × List Bool → Bool),
      IsPolyTime R ∧
      (∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w)) ∧
      ∀ x w w', w.length ≤ p.eval x.length → w'.length ≤ p.eval x.length →
        R (x, w) → R (x, w') → w = w' }

/-- A **proof system** for `L` in the sense of Cook and Reckhow [CR79]: a polynomial-time
function whose range is exactly `L`; `π` is a proof of `y` when `P π = y`. -/
def IsProofSystem (L : DecisionProblem) (P : List Bool → List Bool) : Prop :=
  IsPolyTime P ∧ ∀ y, L y ↔ ∃ π, P π = y

/-- `P` **p-simulates** `Q`: a polynomial-time translation turns `Q`-proofs into `P`-proofs
of the same statements. -/
def PSimulates (P Q : List Bool → List Bool) : Prop :=
  ∃ h : List Bool → List Bool, IsPolyTime h ∧ ∀ π, P (h π) = Q π

/-- `P` is a **p-optimal** proof system for `L`: a proof system that p-simulates every proof
system for `L`. -/
def IsPOptimalProofSystem (L : DecisionProblem) (P : List Bool → List Bool) : Prop :=
  IsProofSystem L P ∧ ∀ Q, IsProofSystem L Q → PSimulates P Q

/-- A **total NP search problem**: a polynomial-time relation `R` such that every input `x` has
a solution `y` of length at most `p |x|`. -/
structure TFNPProblem where
  /-- The polynomial-time verification relation. -/
  R : List Bool × List Bool → Bool
  /-- The bound on solution lengths. -/
  p : Polynomial ℕ
  polyTime : IsPolyTime R
  total : ∀ x, ∃ y : List Bool, y.length ≤ p.eval x.length ∧ R (x, y)

/-- `S` **reduces** to `T` (polynomial-time many-one reduction of search problems, [Pa94]):
`f` maps instances of `S` to instances of `T` and `g` maps solutions back. -/
def TFNPProblem.Reduces (S T : TFNPProblem) : Prop :=
  ∃ (f : List Bool → List Bool) (g : List Bool × List Bool → List Bool),
    IsPolyTime f ∧ IsPolyTime g ∧
    ∀ x y, y.length ≤ T.p.eval (f x).length → T.R (f x, y) →
      (g (x, y)).length ≤ S.p.eval x.length ∧ S.R (x, g (x, y))

/-- `T` is a **complete** total NP search problem. -/
def TFNPProblem.IsComplete (T : TFNPProblem) : Prop :=
  ∀ S : TFNPProblem, S.Reduces T

/-- Every language reduces to itself. -/
@[category API, AMS 3 68]
lemma manyOneReducible_refl (A : DecisionProblem) : ManyOneReducible A A :=
  ⟨id, isPolyTime_id, fun _ => rfl⟩

/-- Every proof system p-simulates itself. -/
@[category API, AMS 3 68]
lemma pSimulates_refl (P : List Bool → List Bool) : PSimulates P P :=
  ⟨id, isPolyTime_id, fun _ => rfl⟩

/-- A complete language for `C` belongs to `C`. -/
@[category API, AMS 3 68]
lemma IsCompleteFor.mem {C : DecisionComplexityClass} {L : DecisionProblem}
    (h : IsCompleteFor C L) : L ∈ C :=
  h.1

/-- Unambiguous verifiers are in particular NP verifiers. -/
@[category API, AMS 3 68]
lemma UP_subset_NP : UP ⊆ NP := by
  rintro L ⟨p, R, hR, hL, -⟩
  exact ⟨p, R, hR, hL⟩

/--
**SAT has no p-optimal proof system** (Pudlák's conjecture `SAT` [Pu17]).

No proof system for `SAT` p-simulates every other proof system for `SAT`. Since the existence of
a p-optimal proof system depends only on the polynomial-time many-one degree of the language
[KMT03], the conjecture is stated here for an arbitrary NP-complete language. Equivalently
[Pu17], for every consistent polynomial-time axiomatized theory `T ⊇ S¹₂` there is a proof
system for `SAT` whose soundness `T` cannot prove.
-/
@[category research open, AMS 3 68]
theorem sat_no_p_optimal_proof_system (L : DecisionProblem) (hL : IsCompleteFor NP L) :
    ¬∃ P : List Bool → List Bool, IsPOptimalProofSystem L P := by
  sorry

/--
**TFNP has no complete problem** (Megiddo–Papadimitriou [MP91]; Pudlák's conjecture `TFNP`
[Pu17]).

No total NP search problem is complete under polynomial-time many-one reductions of search
problems. Equivalently [Pu17], for every consistent polynomial-time axiomatized theory
`T ⊇ S¹₂` some total NP search problem is not provably total in `T`.
-/
@[category research open, AMS 3 68]
theorem tfnp_no_complete_problem : ¬∃ T : TFNPProblem, T.IsComplete := by
  sorry

/--
**UP has no complete language** (Hartmanis–Hemachandra [HH88]; Pudlák's conjecture `UP`
[Pu17]).

No language accepted by an unambiguous polynomial-time verifier is complete for `UP` under
polynomial-time many-one reductions.
-/
@[category research open, AMS 3 68]
theorem up_no_complete_language : ¬∃ L : DecisionProblem, IsCompleteFor UP L := by
  sorry

/--
**NP ∩ coNP has no complete language** (Pudlák's conjecture `NP ∩ coNP` [Pu17]).

No language in `NP ∩ coNP` is complete for that class under polynomial-time many-one
reductions.
-/
@[category research open, AMS 3 68]
theorem np_inter_conp_no_complete_language :
    ¬∃ L : DecisionProblem, IsCompleteFor (NP ∩ coNP) L := by
  sorry

/--
**If `NP = coNP` then TFNP has a complete problem** [MP91, Pu17].

Under `NP = coNP` the search problem "given a CNF, find a satisfying assignment or a short
proof of unsatisfiability" is total and complete.
-/
@[category research solved, AMS 3 68]
theorem tfnp_no_complete_problem.variants.exists_of_NP_eq_coNP (h : NP = coNP) :
    ∃ T : TFNPProblem, T.IsComplete := by
  sorry

/--
**The conjecture implies `NP ≠ coNP`** [Pu17].
-/
@[category research solved, AMS 3 68]
theorem tfnp_no_complete_problem.variants.NP_ne_coNP
    (h : ¬∃ T : TFNPProblem, T.IsComplete) : NP ≠ coNP :=
  fun heq => h (tfnp_no_complete_problem.variants.exists_of_NP_eq_coNP heq)

/--
**If `P = NP` then every NP-complete language has a p-optimal proof system.**

The map sending `π` to itself when `π ∈ L` and to a fixed element of `L` otherwise is then
polynomial-time, and every proof system `Q` for `L` is p-simulated by it via `Q` itself.
-/
@[category textbook, AMS 3 68]
theorem sat_no_p_optimal_proof_system.variants.exists_of_P_eq_NP (h : P = NP)
    (L : DecisionProblem) (hL : IsCompleteFor NP L) (hne : ∃ y, L y = true) :
    ∃ P : List Bool → List Bool, IsPOptimalProofSystem L P := by
  sorry

end PudlakFiniteDomain
