import FormalConjectures.Util.Answer

section WithAuxiliary

open Google

open Lean Elab Meta

set_option google.answer "with_auxiliary"

open Lean Elab Meta

#guard_msgs in
theorem foo : answer(True) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `foo._answer | throwError "here"
  trivial

#guard_msgs in
theorem bar : 1 = answer(sorry) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = 1 = bar._answer
  sorry


#guard_msgs in
theorem bar_symm : answer(sorry) = 1 := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = bar_symm._answer = 1
  sorry

end WithAuxiliary

section AlwaysTrue

set_option google.answer "always_true"

theorem this_works : (answer(sorry) : Prop) := by
  trivial

end AlwaysTrue
