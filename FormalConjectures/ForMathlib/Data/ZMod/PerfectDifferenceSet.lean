import Mathlib.Data.ZMod.Defs

/--
A perfect difference set modulo `n` is a set `D` such that the map `(a, b) ↦ a - b` from
`D.offDiag` to `{x : ZMod n | x ≠ 0}` is a bijection.
-/
def IsPerfectDifferenceSet (D : Set ℕ) (n : ℕ) : Prop :=
  D.offDiag.BijOn (fun (a, b) => (a - b : ZMod n)) {x : ZMod n | x ≠ 0}
