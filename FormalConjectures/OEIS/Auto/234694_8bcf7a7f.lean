/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A234694: $a(n) = |\{0 < k < n: p = k + \mathrm{prime}(n-k) \text{ and } \mathrm{prime}(p) - p + 1 \text{ are both prime}\}|$.
We interpret $\mathrm{prime}(m)$ as the $m$-th prime number $p_m$, which is $\mathrm{Nat.nth} \ \mathrm{Nat.Prime} \ (m-1)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The finite set of indices k is {k : ℕ | 1 ≤ k < n} = Ico 1 n.
  (filter (fun k =>
    -- m is the index for the n-k-th prime
    let m : ℕ := n - k

    -- Since k ∈ Ico 1 n, m ≥ 1. The (n-k)-th prime is at 0-index m-1.
    let p_m : ℕ := Nat.nth Nat.Prime (m - 1)
    let p : ℕ := k + p_m

    -- Since p is a candidate prime, p must be at least 2. The p-th prime is at 0-index p-1.
    let p_th_prime : ℕ := Nat.nth Nat.Prime (p - 1)

    Nat.Prime p ∧ Nat.Prime (p_th_prime - p + 1)
  ) (Ico 1 n)).card

-- Helper definition for the p-th prime (0-indexed by p-1)
noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

/--
Conjecture part (i) of A234694 implies that there are infinitely many primes $p$ with
$\mathrm{prime}(p) - p + 1$ (or $\mathrm{prime}(p) + p + 1$) also prime.
-/
theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := by
  sorry
