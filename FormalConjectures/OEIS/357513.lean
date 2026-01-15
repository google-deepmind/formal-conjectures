import FormalConjectures.Util.ProblemImports

open Nat

/--
A357513: $a(n) = \text{numerator of } \sum_{k = 1..n} \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2 \text{ for } n \ge 1 \text{ with } a(0) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun k : ℕ =>
    let k_q : ℚ := k
    let choose_nk_sq : ℚ := (Nat.choose n k : ℚ) ^ 2
    let choose_npkk_sq : ℚ := (Nat.choose (n + k) k : ℚ) ^ 2
    (choose_nk_sq * choose_npkk_sq) / k_q ^ 3
  ).num.natAbs


/--
Conjecture based on A357513 F-Lines: $a(p-1) \equiv 0 \pmod{p^4}$ for all primes $p \ge 3$ except $p=7$ (checked up to $p=499$).
We formalize the specific conjecture presented in the OEIS entry.
-/
@[category research open, AMS 11]
theorem a357513_supercongruence (p : ℕ) (hp : Nat.Prime p) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4] := by
  sorry
