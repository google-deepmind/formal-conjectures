import FormalConjectures.Util.Linters.ExistsImplicationLinter

/--
warning: Declaration contains the pattern the expression ∃ n, n ≠ 0 → False. Did you mean ∃ n, n ≠ 0 ∧ False?

Note: This linter can be disabled with `set_option linter.style.existsImplication false`
---
info: Nat
-/
#guard_msgs in
theorem this_doesnt_look_good : ∃ n : Nat, n ≠ 0 → False := by
  use 0
  trivial

/--
warning: Declaration contains the pattern the expression ∃ n, n ≠ 0 → n ≠ 1 → False. Did you mean ∃ n, n ≠ 0 ∧ n ≠ 1 ∧ False?

Note: This linter can be disabled with `set_option linter.style.existsImplication false`
---
info: Nat
-/
#guard_msgs in
theorem even_worse : ∃ n : Nat, n ≠ 0 → n ≠ 1 → False := by
  use 0
  trivial

#guard_msgs in
theorem this_is_fine : ∃ n : Nat, n ≠ 0 ∨ False := by
  sorry
