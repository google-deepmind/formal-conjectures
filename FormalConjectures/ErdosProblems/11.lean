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

/--
Erdős often asked this under the weaker assumption that n
is not divisible by 4
.
-/
@[category research open, AMS 11]
theorem erdos_11_i (n : ℕ) (hn : Odd n) (hn_2 : n % 4 ≠ 0):
    ∃ k l : ℕ , Squarefree k ∧ n = k + 2**l := by
  sorry

/--
Erdős thought that proving this with two powers of 2 is perhaps easy, and could prove that it is true (with a single power of two) for almost all n.
-/
@[category research open, AMS 11]
theorem erdos_11_ii (n : ℕ) (hn : Odd n):
    ∃ k l m: ℕ , Squarefree k ∧ n = k + 2**l + 2**m := by
  sorry
