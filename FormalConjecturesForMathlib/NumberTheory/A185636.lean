/-
Conjecture: (OEIS A185636, Zhi-Wei Sun)
For each n ∈ ℕ, there exists k ∈ {0, ..., n} such that both n + k and n + k^2 are prime.

Reference: https://oeis.org/A185636
Status: Open (as of January 2026)
Prize: $100 offered by Zhi-Wei Sun (see his homepage)
Numerical evidence: Verified for large n, no counterexamples known.

Prerequisites: Basic number theory, primality.
-/

import data.nat.prime

open nat

/-- 
For every natural number n, there exists k ≤ n such that both n + k and n + k^2 are prime.
-/
conjecture sun_A185636 :
  ∀ n : ℕ, ∃ k : ℕ, k ≤ n ∧ prime (n + k) ∧ prime (n + k^2)