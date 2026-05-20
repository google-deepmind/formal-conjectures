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
open Set
open Nat

/--
A055487: Least $m$ such that $\phi(m) = n!$.
The sequence $a(n)$ is the smallest natural number $m$ such that Euler's totient function
$\phi(m)$ equals $n!$.
-/
noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}


theorem a_one : A055487 1 = 1 := by
  norm_num [A055487]
  apply ((Nat.isLeast_find ⟨(1),by simp_all⟩ ) ).csInf_eq

theorem a_two : A055487 2 = 3 := by
  norm_num [A055487]
  apply((Nat.isLeast_find ⟨3,by constructor⟩) ).csInf_eq

theorem a_three : A055487 3 = 7 := by
  simp_all [A055487]
  apply((Nat.isLeast_find ⟨7,by constructor⟩) ).csInf_eq

theorem a_four : A055487 4 = 35 := by
  norm_num [A055487]
  apply Nat.isLeast_find ⟨35,↑rfl⟩|>.csInf_eq

/-- The set of primes $p > \sqrt{n!}$ such that $p-1$ divides $n!$ and $n!/(p-1) + 1$ is also prime. -/
def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  -- Note: Nat.Prime p implies p ≥ 2, so p - 1 ≥ 1.
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

/--
A055487 Conjecture: Unless n!+1 is prime (i.e., n in A002981), a(n)=pq where p is the least prime > sqrt(n!) such that (p-1) | n! and q=n!/(p-1)+1 is prime.
-/
theorem A055487_conjecture (n : ℕ)
    (h_not_prime : ¬Nat.Prime (Nat.factorial n + 1))
    (h_solvable : (prime_candidates n).Nonempty) :
    A055487 n =
      let N := Nat.factorial n
      let p := sInf (prime_candidates n)
      p * (N / (p - 1) + 1) :=
  by sorry
