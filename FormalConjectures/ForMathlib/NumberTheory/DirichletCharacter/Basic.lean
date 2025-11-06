import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace DirichletCharacter

instance {S : Type*} [DecidableEq S] [CommRing S] {m : ℕ} :
    DecidablePred (Odd  (S := S) (m := m)) :=
  fun ψ ↦ decidable_of_iff (ψ (-1) = -1) <| by rfl

instance {S : Type*} [DecidableEq S] [CommRing S] {m : ℕ} :
    DecidablePred (Even (S := S) (m := m)) :=
  fun ψ ↦ decidable_of_iff (ψ (-1) = 1) <| by rfl

end DirichletCharacter
