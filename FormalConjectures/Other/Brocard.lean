import Mathlib

/--
Brocard’s (Ramanujan’s) conjecture.

The only natural numbers `n` such that `n! + 1` is a perfect square
are `n = 4`, `n = 5`, and `n = 7`.
-/
axiom brocard_conjecture :
  ∀ n m : ℕ,
    n.factorial + 1 = m^2 →
    n = 4 ∨ n = 5 ∨ n = 7
