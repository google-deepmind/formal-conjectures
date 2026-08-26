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

import FormalConjecturesUtil

/-!
# Least prime $\ge n$

Least prime $\ge n$ (version 1 of the "next prime" function).

*References:*
- [A007918](https://oeis.org/A007918)
-/

namespace OeisA7918

/-- Least prime $\ge n$ (version 1 of the "next prime" function). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { p : ℕ | p.Prime ∧ n ≤ p }

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 0 ≤ p } 2 :=
    ⟨⟨Nat.prime_two, Nat.zero_le 2⟩, fun p hp ↦ hp.1.two_le⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 1 ≤ p } 2 :=
    ⟨⟨Nat.prime_two, by decide⟩, fun p hp ↦ hp.1.two_le⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 2 ≤ p } 2 :=
    ⟨⟨Nat.prime_two, le_rfl⟩, fun p hp ↦ hp.1.two_le⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 3 ≤ p } 3 :=
    ⟨⟨Nat.prime_three, le_rfl⟩, fun p hp ↦ hp.2⟩
  exact h.csInf_eq

/--
The initial term $p_0$ and common difference $d$ form an arithmetic progression of
length $n$ consisting entirely of prime numbers with $d > 0$.
-/
def isApOfNPrimes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, (p0 + k * d).Prime

/--
According to the "k-tuple" conjecture, $a(n)$ is the initial term of the
lexicographically earliest increasing arithmetic progression of $n$ primes;
the corresponding common differences are given by A061558.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 0 < n) :
    a n = sInf { p0 : ℕ | ∃ d : ℕ, isApOfNPrimes n p0 d } := by
  sorry

/--
If $n > 1$, then $a(n) < n^{n^{1/n}}$.
- Thomas Ordowski, Feb 23 2023
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  sorry

end OeisA7918
