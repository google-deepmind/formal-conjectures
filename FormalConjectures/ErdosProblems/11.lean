import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Squarefree

*Reference:* [erdosproblems.com/11](https://www.erdosproblems.com/11)
-/
/--
Is every odd n the sum of a squarefree number and a power of 2?
-/
@[category research open, AMS 11]
theorem erdos_11 (n : ℕ) (hn : Odd n) :
    ∃ k l : ℕ , Squarefree k ∧ n = k + 2**l := by
  sorry
