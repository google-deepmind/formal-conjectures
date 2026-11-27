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
# Conjectures in Complexity Theory

This file contains formal statements of some of the main open conjectures
in complexity theory, including

- the P vs NP problem
- the NP vs coNP problem
- the P vs BPP problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/P_versus_NP_problem)
- [The Clay Institute](https://www.claymath.org/millennium/p-vs-np/)
-/

@[expose] public section

namespace ComplexityTheory

/--
**P ≠ NP**:

The conjecture that the complexity classes P and NP are not equal.
-/
@[category research open, AMS 68]
theorem P_ne_NP : P ≠ NP := by sorry

/--
**NP ≠ coNP**:

The conjecture that the complexity classes NP and coNP are not equal.
-/
@[category research open, AMS 68]
theorem NP_ne_coNP : NP ≠ coNP := by sorry

/--
**P = BPP**:

The conjecture that the complexity classes P and BPP are equal.
-/
@[category research open, AMS 68]
theorem P_eq_BPP : P = BPP := by sorry

open Computability Turing in
/-- The machine of `M`, with its output-alphabet equivalence composed with `Equiv.boolNot`,
decides `fun a => !f a`. -/
def tm2ComputableInPolyTimeNot {α Γ : Type} {ea : α → List Γ} {f : α → Bool}
    (M : TM2ComputableInPolyTime ea (fun b : Bool => [b]) f) :
    TM2ComputableInPolyTime ea (fun b : Bool => [b]) (fun a => !f a) where
  tm := M.tm
  inputAlphabet := M.inputAlphabet
  outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
  time := M.time
  outputsFun a := by
    have := M.outputsFun a
    simpa [Equiv.boolNot] using this

/-- `P` is closed under complement. -/
@[category API, AMS 68]
theorem compl_mem_P {L : DecisionProblem} (h : L ∈ P) : Lᶜ ∈ P :=
  h.elim fun M => ⟨tm2ComputableInPolyTimeNot M⟩

/--
The theorem that the set of complements of languages in P is itself P.

This can be proven by observing that the boolean negation function is computable in polynomial time,
and that compositions of poly-time computable functions are also poly-time computable.
-/
@[category textbook, AMS 68]
theorem coP_eq_P :
    { L | Lᶜ ∈ P } = P := by
  ext L
  refine ⟨fun h => ?_, compl_mem_P⟩
  simpa using compl_mem_P h

/--
The theorem that P is a subset of NP.

This can be proven by observing that for any language in P,
we can construct a verifier that ignores the witness and simply runs the poly-time decider for the
language.
-/
@[category textbook, AMS 68, formal_proof using lean4 at
  "https://github.com/AItoBit/p-subset-np/blob/beaeee15c37af6efac518426e117861c00ff3acc/PSubsetNP.lean#L358"]
theorem P_subset_NP :
    P ⊆ NP := by
  sorry

/--
The theorem that P is a subset of coNP.
-/
@[category textbook, AMS 68]
theorem P_subset_coNP :
    P ⊆ coNP := by
  rw [coNP, ← coP_eq_P]
  simp only [Set.ofPred_subset_ofPred]
  intros L hL
  exact P_subset_NP hL

/--
The theorem that P is a subset of BPP.

This can be proven by observing that for any language in P,
we can construct a randomized decider that ignores the random bits
and simply runs the poly-time decider for the language.
-/
@[category textbook, AMS 68]
theorem P_subset_BPP :
    P ⊆ BPP := by
  sorry

end ComplexityTheory
