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
module

public meta import FormalConjecturesForMathlib.Computability.CounterexampleSearch
public import FormalConjecturesForMathlib.Computability.CounterexampleSearch
public import FormalConjecturesForMathlib.Computability.CounterexampleCertificate
public import FormalConjecturesForMathlib.Computability.ClockedEvaluation
public import FormalConjecturesForMathlib.Computability.EncodedCandidates

/-! # Regression proofs for finite testing, minimization, and coverage certificates -/

@[expose] public section

namespace Computability.FiniteTests.Test

open Enumeration

def prefixCheck (a x : ℕ) : Bool := decide (x ≤ a)

/-- Finite fitting permits a different candidate at each bound. -/
theorem finite_fitting : ∀ n, ∃ a, Survives naturals prefixCheck a n := by
  intro n
  refine ⟨n, ?_⟩
  simp [survives_iff, naturals, prefixCheck]

/-- No candidate in this family works uniformly. -/
theorem no_uniform_candidate : ¬ ∃ a, Correct prefixCheck a := by
  rintro ⟨a, h⟩
  have := h (a + 1)
  simp [prefixCheck] at this

theorem excludes_prefix_iff (s n : ℕ) :
    Excludes naturals naturals prefixCheck s n ↔ s < n := by
  constructor
  · intro h
    obtain ⟨x, hx, hf⟩ := h s (naturals.covers s)
    have hx' : x ≤ n := naturals.mem_upTo.mp hx
    simp only [prefixCheck, decide_eq_false_iff_not, not_le] at hf
    omega
  · intro h a ha
    have ha' : a ≤ s := naturals.mem_upTo.mp ha
    refine ⟨n, naturals.covers n, ?_⟩
    simp only [prefixCheck, decide_eq_false_iff_not]
    omega

/-- The partial search has the exact least value on the quantifier counterexample. -/
theorem least_bound (s : ℕ) :
    s + 1 ∈ counterexampleBound naturals naturals prefixCheck s := by
  rw [mem_counterexampleBound]
  simp only [excludes_prefix_iff]
  constructor
  · omega
  · intro m hm
    omega

example : (bitstrings.upTo 0).card = 1 := by decide
example : (bitstrings.upTo 3).card = 15 := by decide
example : [true, false, true] ∈ bitstrings.upTo 3 := by decide
example : [true, false, true] ∉ bitstrings.upTo 2 := by decide
example : survives naturals prefixCheck 2 2 = true := by decide
example : survives naturals prefixCheck 2 3 = false := by decide
example : excludes naturals naturals prefixCheck 2 2 = false := by decide
example : excludes naturals naturals prefixCheck 2 3 = true := by decide

def noCandidates : Enumeration Empty where
  size := Empty.elim
  upTo _ := ∅
  mem_upTo := by intro a; exact a.elim

example : excludes noCandidates naturals (fun a ↦ a.elim) 0 0 = true := by decide

example : validateCertificate naturals naturals prefixCheck 2 3
    [(0, 1), (1, 2), (2, 3)] = true := by decide
-- Missing candidate, duplicated key, corrupted witness, and a witness outside the bound.
example : validateCertificate naturals naturals prefixCheck 2 3
    [(0, 1), (2, 3)] = false := by decide
example : validateCertificate naturals naturals prefixCheck 2 3
    [(0, 1), (1, 2), (1, 2)] = false := by decide
example : validateCertificate naturals naturals prefixCheck 2 3
    [(0, 1), (1, 2), (2, 3), (2, 3)] = false := by decide
example : validateCertificate naturals naturals prefixCheck 2 3
    [(0, 1), (1, 1), (2, 3)] = false := by decide
example : validateCertificate naturals naturals prefixCheck 2 2
    [(0, 1), (1, 2), (2, 3)] = false := by decide
-- A certificate for a restricted prefix cannot certify a larger prefix.
example : validateCertificate naturals naturals prefixCheck 3 3
    [(0, 1), (1, 2), (2, 3)] = false := by decide

open ClockedEvaluation

def countdown : ℕ → State ℕ
  | 0 => .halted false
  | n + 1 => .running n

example : Clock.ofNat 0 2 = none := by decide
example : (Clock.ofNat 1 0).isSome = true := by decide
example : (Clock.mk 2 0 (by decide)).bound 0 = 2 := by decide
example : (Clock.mk 2 0 (by decide)).bound 100 = 2 := by decide
example : (Clock.mk 3 2 (by decide)).bound 2 = 27 := by decide
example : run countdown 2 (.running 2) = .timeout := by decide
example : run countdown 3 (.running 2) = .halted false := by decide
example : run countdown 4 (.running 2) = .halted false := by decide
example : run countdown 0 (.halted true) = .halted true := by decide
example : run countdown 0 (.invalid) = .invalid := by decide
example : Outcome.timeout.passes false = false := by decide
example : Outcome.timeout.passes true = false := by decide
example : Outcome.invalid.passes false = false := by decide
example : (Outcome.halted false).passes true = false := by decide
example : (Outcome.halted true).passes false = false := by decide
example : checkWithin countdown ⟨3, 0, by decide⟩ 0 (.running 2) false = true := by decide
example : checkWithin countdown ⟨2, 0, by decide⟩ 0 (.running 2) false = false := by decide

open BitstringEncoding

def encodedCandidate : ClockedCode ℕ := ⟨5, ⟨2, 0, by decide⟩⟩

example : decodeCanonical (α := Bool) [] = none := by decide
example : decodeCanonical (α := Bool) [true] = some true := by decide
example : decodeCanonical (α := ℕ) [false, false] = none := by decide
example : (ofBitstringEncoding (α := Bool)).upTo 0 = ∅ := by decide
example : ((ofBitstringEncoding (α := Bool)).upTo 1).card = 2 := by decide
example : bitDecode (bitEncode encodedCandidate) = some encodedCandidate := by decide
example : bitDecode (α := ClockedCode ℕ) (bitEncode ((5, 0, 2) : ℕ × ℕ × ℕ)) = none := by
  decide
example : (bitEncode (ClockedCode.mk 5 ⟨1, 0, by decide⟩)).length <
    (bitEncode (ClockedCode.mk 5 ⟨8, 0, by decide⟩)).length := by decide
example : (bitEncode (ClockedCode.mk 5 ⟨1, 0, by decide⟩)).length <
    (bitEncode (ClockedCode.mk 5 ⟨1, 8, by decide⟩)).length := by decide

theorem encoded_candidate_covered : encodedCandidate ∈
    (ofBitstringEncoding (α := ClockedCode ℕ)).upTo (bitEncode encodedCandidate).length :=
  (ofBitstringEncoding (α := ClockedCode ℕ)).covers encodedCandidate

/-- info: (true, false) -/
#guard_msgs in
#eval (survives naturals prefixCheck 2 2, survives naturals prefixCheck 2 3)

/-- info: 3 -/
#guard_msgs in
#eval (counterexampleBound naturals naturals prefixCheck 2).get
  ((counterexampleBound_dom naturals naturals prefixCheck 2).mpr ⟨3, by decide⟩)

end Computability.FiniteTests.Test
