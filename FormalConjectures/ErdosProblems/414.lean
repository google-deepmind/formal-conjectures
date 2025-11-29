/-
Formailisation of E.C. 414
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 386

*References:*
- [erdosproblems.com/386](https://www.erdosproblems.com/386)
-/

namespace Erdos386

/-
This is the structure of the equation:
-/

def erdos_386_equation (a b : ℕ) (A : Finset ℕ) :=
  Nat.choose a b = ∏ α ∈ A, α

#eval Nat.divisors 3
#eval Nat.divisors 3
/-
The following set contains all solutions `(n, k, P)` to the Erdős problem 386.
A solution is a tuple `(n, k, P)`, where `n ≥ 2` and `k` are an integers and `P`
is a non-empty finite set of
distinct prime numbers, such that it's product is binomial coefficient n choose k.
-/
def erdos_386_solutions : Set (ℕ × ℕ × Finset ℕ) := {
  (n, k, P) |
    (n ≥ 2 ∧ 2 ≤ k ∧ k ≤ n - 2) ∧
    P.Nonempty ∧
    (∀ p ∈ P, p.Prime) ∧
    erdos_386_equation n k P
  }
/--
Erdos 386 Conjecture:
Are there infinitely many tuples `(n, k, P)`, where `n` and `k` are integers satisfying
`n ≥ 2`, `2 ≤ k ≤ n - 2` and `P` is a set of distinct primes such that the following equation holds:
\[ {n}\choose{k} = \prod_{p \in P} p \] ?
-/
@[category research open, AMS 11]
theorem erdos_386_conjecture : erdos_386_solutions.Infinite ↔ answer(sorry) := by
  sorry

@[category test, AMS 11]
theorem erdos_386_example :
  (21, 2, ({2, 3, 5, 7} : Finset ℕ)) ∈ erdos_386_solutions := by
  simp [erdos_386_solutions, erdos_386_equation, Nat.choose]
  decide


end Erdos386
