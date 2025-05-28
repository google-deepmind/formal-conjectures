import FormalConjectures.Util.ProblemImports

/-!
# Collatz conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
-/
/--
Consider the following operation on an arbitrary integer:
If the number is even, divide it by two.
If the number is odd, triple it and add one.
Formally, we define the function f as follows:
-/
def f (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/--
Now form a sequence by performing this operation repeatedly, beginning with any positive integer,
and taking the result at each step as the input at the next.
The **Collatz conjecture** states that for any positive integer $n$, there exists a natural number
$i$ such that the $i$-th term of the sequence is 1.
-/
@[category research open, AMS 11]
theorem CollatzConjecture : ∀ n : ℕ, n > 0 → ∃ i : ℕ, Nat.iterate f i n = 1 := by
  sorry
