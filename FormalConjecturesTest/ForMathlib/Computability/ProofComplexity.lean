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
import FormalConjecturesForMathlib.Computability.ExtendedFrege
import FormalConjecturesForMathlib.Computability.CookReckhow

/-! # Kernel tests for propositional syntax and proof checking -/

namespace ProofComplexityTest

open PropositionalProof PropositionalProof.Formula
open BitstringEncoding

private def p : Formula := .var 0
private def q : Formula := .var 1
private def r : Formula := .var 2

example (a : Formula) : bitDecode (bitEncode a) = some a := bitDecode_bitEncode a
example (a : List Formula) : bitDecode (bitEncode a) = some a := bitDecode_bitEncode a
example : (bitDecode [] : Option Formula) = none := by decide +kernel
example : (bitDecode [true] : Option Formula) = none := by decide +kernel
example : ofTokens [] = none := by decide +kernel
example : ofTokens [0] = none := by decide +kernel
example : ofTokens [1, 2] = none := by decide +kernel
example : ofTokens [2, 2] = none := by decide +kernel
example : ofTokens [0, 1, 2, 3] = some (.neg (.imp p q)) := by decide +kernel
example : parse 0 [2] = none := by decide +kernel
example : parse 1 [2, 3] = some (p, [3]) := by decide +kernel
example : parse 1 [1, 2, 3] = none := by decide +kernel
example : parse 2 [1, 2, 3] = some (.imp p q, []) := by decide +kernel
example : (.var 1024 : Formula).size > p.size := by decide +kernel
example : (Formula.imp p p).nodes = 3 := by decide +kernel
example : (Formula.imp p p).size > p.size := by decide +kernel
example : (Formula.imp p p).Tautology := by decide +kernel
example : ¬ p.Tautology := by decide +kernel
example : ¬ (Formula.neg (.imp p p)).Tautology := by decide +kernel
example : (Formula.iff p q).eval (fun _ => false) = true := by decide +kernel
example : (Formula.iff p q).eval (fun v => decide (v = 0)) = false := by decide +kernel
example : (Formula.imp p q).support = {0, 1} := by decide +kernel
example : (Formula.imp p p).subst (fun _ => q) = .imp q q := by decide +kernel

example (a b : Formula) : Frege.axiom1 (.imp a (.imp b a)) = true := by
  simp [Frege.axiom1]
example (a b c : Formula) :
    Frege.axiom2 (.imp (.imp c (.imp b a)) (.imp (.imp c b) (.imp c a))) = true := by
  simp [Frege.axiom2]
example (a b d : Formula) :
    Frege.axiom3 (.imp (.imp d (.imp b a)) (.imp b (.imp d a))) = true := by
  simp [Frege.axiom3]
example (a b : Formula) :
    Frege.axiom4 (.imp (.imp b a) (.imp (.neg a) (.neg b))) = true := by
  simp [Frege.axiom4]
example (a : Formula) : Frege.axiom5 (.imp (.neg (.neg a)) a) = true := by
  simp [Frege.axiom5]
example (a : Formula) : Frege.axiom6 (.imp a (.neg (.neg a))) = true := by
  simp [Frege.axiom6]

example : Frege.axiom1 (.imp p (.imp q r)) = false := by decide +kernel
example : Frege.axiom2
    (.imp (.imp r (.imp q p)) (.imp (.imp p q) (.imp r p))) = false := by decide +kernel
example : Frege.axiom2
    (.imp (.imp r (.imp q p)) (.imp (.imp r q) (.imp p p))) = false := by decide +kernel
example : Frege.axiom2
    (.imp (.imp r (.imp q p)) (.imp (.imp r r) (.imp r p))) = false := by decide +kernel
example : Frege.axiom2
    (.imp (.imp r (.imp q p)) (.imp (.imp r q) (.imp r r))) = false := by decide +kernel
example : Frege.axiom3
    (.imp (.imp r (.imp q p)) (.imp q (.imp p p))) = false := by decide +kernel
example : Frege.axiom3
    (.imp (.imp r (.imp q p)) (.imp r (.imp r p))) = false := by decide +kernel
example : Frege.axiom3
    (.imp (.imp r (.imp q p)) (.imp q (.imp r r))) = false := by decide +kernel
example : Frege.axiom4 (.imp (.imp q p) (.imp (.neg q) (.neg q))) = false := by decide +kernel
example : Frege.axiom4 (.imp (.imp q p) (.imp (.neg p) (.neg p))) = false := by decide +kernel
example : Frege.axiom5 (.imp (.neg (.neg p)) q) = false := by decide +kernel
example : Frege.axiom6 (.imp p (.neg (.neg q))) = false := by decide +kernel
example : Frege.isAxiom (.imp p p) = false := by decide +kernel
example : Frege.modusPonens [p, .imp p q] q = true := by decide +kernel
example : Frege.modusPonens [.imp p q] q = false := by decide +kernel
example : Frege.modusPonens [p] q = false := by decide +kernel
example : Frege.modusPonens [q, .imp p q] p = false := by decide +kernel
example : Frege.modusPonens [] p = false := by decide +kernel

/-- A five-line Hilbert derivation of reflexive implication. -/
def identityProof (a : Formula) : List Formula :=
  [ .imp a (.imp (.imp a a) a),
    .imp a (.imp a a),
    .imp (.imp a (.imp (.imp a a) a))
      (.imp (.imp a (.imp a a)) (.imp a a)),
    .imp (.imp a (.imp a a)) (.imp a a),
    .imp a a ]

theorem identityProof_checked : fregeProof (.imp p p) (identityProof p) = true := by decide +kernel
example : extendedFregeProof (.imp p p) (identityProof p) = true := by decide +kernel
example : fregeProof (.imp p p) [] = false := by decide +kernel
example : extendedFregeProof (.imp p p) [] = false := by decide +kernel
example : fregeProof (.imp p p) [.imp p p] = false := by decide +kernel
example : fregeProof q (identityProof p) = false := by decide +kernel
example : fregeProof (.imp p p) (identityProof p).reverse = false := by decide +kernel
example : fregeProof p [p, .imp p p, p] = false := by decide +kernel
example : proofSize (identityProof p) > (identityProof p).length := by decide +kernel
example : proofSize [] = 0 := by decide +kernel
example : proofSize [p, p] > proofSize [p] := by decide +kernel

private def ext : Formula := Formula.iff q p

example : extensionData ext = some (1, p) := by decide +kernel
example : extensionData (.imp q p) = none := by decide +kernel
example : extensionData (.neg (.imp (.imp q p) (.neg (.imp r q)))) = none := by decide +kernel
example : extensionData (.neg (.imp (.imp q p) (.neg (.imp p r)))) = none := by decide +kernel
example : extensionStep (.imp p p) [] ext = true := by decide +kernel
example : extensionStep p [] (Formula.iff q q) = false := by decide +kernel
example : extensionStep q [] ext = false := by decide +kernel
example : extensionStep p [q] ext = false := by decide +kernel
example : extensionStep p [.neg q] ext = false := by decide +kernel
example : extensionStep p [ext] ext = false := by decide +kernel
example : extensionStep p [ext] (Formula.iff r q) = true := by decide +kernel
example : extensionStep p [ext] (Formula.iff r (.imp q r)) = false := by decide +kernel
example : ¬ ext.Tautology := by decide +kernel
example : extendedFregeProof ext [ext] = false := by decide +kernel
example : extendedFregeProof q [ext, q] = false := by decide +kernel

/-- A valid extension is used in modus ponens before a Frege proof of the conclusion. -/
def extensionProof : List Formula :=
  [ext, .imp ext (.imp p ext), .imp p ext] ++ identityProof p

theorem extensionProof_checked : extendedFregeProof (.imp p p) extensionProof = true := by decide +kernel
theorem extensionProof_not_frege : fregeProof (.imp p p) extensionProof = false := by decide +kernel
example : extendedFregeProof (.imp p p) (ext :: ext :: identityProof p) = false := by decide +kernel
example : (Formula.imp p p).Tautology := extendedFregeProof_sound extensionProof_checked

example (f : CookReckhow) : f.PSimulates f := f.psimulates_self
example (f : CookReckhow) (h : f.POptimal) : f.Optimal := CookReckhow.poptimal_implies_optimal h
example (f : CookReckhow) (a : Formula) :
    (∃ w, f.output w = a) ↔ a.Tautology := f.range_iff a

#guard fregeProof (.imp p p) (identityProof p)
#guard extendedFregeProof (.imp p p) extensionProof
#guard !(fregeProof (.imp p p) extensionProof)

end ProofComplexityTest
