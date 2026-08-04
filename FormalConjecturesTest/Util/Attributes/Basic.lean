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

public meta import FormalConjecturesUtil.Attributes.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section


-- The `Category` and `ProblemSubject` attributes

#guard_msgs in
@[category test]
theorem test : 1 + 1 = 2 := by
  sorry

#guard_msgs in
@[category research solved, AMS 11]
theorem FLT : FermatLastTheorem := by
  sorry

#guard_msgs in
open scoped Real in
@[category research open, AMS 11 33]
theorem an_open_problem : Transcendental ℝ (π + rexp 1) := by
  sorry

#guard_msgs in
@[category research solved, formal_proof using lean4 at "https://github.com/example/formal-proof"]
theorem a_formally_solved_problem : 2 + 2 = 4 := by
  rfl

-- formal_proof on non-research categories
#guard_msgs in
@[category textbook, AMS 11, formal_proof using lean4 at "https://github.com/example/proof"]
theorem a_graduate_problem_with_formal_proof : 1 + 1 = 2 := by
  rfl

#guard_msgs in
@[category test, formal_proof using formal_conjectures at ""]
theorem a_test_with_formal_proof : 3 + 3 = 6 := by
  rfl

-- A `formal_proof` link is validated: external kinds must link to the proof, and
-- any link that is given must be a URL.

/--
warning: A `lean4` or `other_system` `formal_proof` should include a link to the proof.
-/
#guard_msgs in
@[category test, formal_proof using lean4 at ""]
theorem a_lean4_proof_with_empty_link : 4 + 4 = 8 := by
  rfl

/--
warning: A `formal_proof` link should be a URL (http:// or https://), but got: "not-a-url".
-/
#guard_msgs in
@[category test, formal_proof using lean4 at "not-a-url"]
theorem a_formal_proof_with_malformed_link : 5 + 5 = 10 := by
  rfl

-- The `#AMS` command

-- `#AMS` currently produces an empty list when compiled: it recovers the subject names with
-- `Lean.findDocString?`, and imported docstrings are only exported at `.server` level, so the
-- lookup finds all 62 constructors and no docstrings. This records that behaviour rather than
-- the intended list; see https://github.com/google-deepmind/formal-conjectures/issues/4733.
/-- info: -/
#guard_msgs in
#AMS
