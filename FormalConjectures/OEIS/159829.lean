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
# Smallest $m$ such that $n^3 + m^3 + 1$ is prime

$a(n)$ is the smallest natural number $m \ge 1$ such that $n^3 + m^3 + 1$ is prime.

*References:*
- [A159829](https://oeis.org/A159829)-/

namespace OeisA159829

/-- $a(n)$ is the smallest natural number $m \ge 1$ such that $n^3 + m^3 + 1$ is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ (n ^ 3 + m ^ 3 + 1).Prime}

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (1 ^ 3 + m ^ 3 + 1).Prime} 1 :=
    ⟨⟨le_rfl, by decide⟩, fun m hm => hm.1⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (2 ^ 3 + m ^ 3 + 1).Prime} 2 :=
    ⟨⟨by decide, by decide⟩, fun m hm => by
      by_contra hc
      have hm1 : 1 ≤ m := hm.1
      have hm2 : m < 2 := not_le.mp hc
      obtain ⟨_, hprime⟩ := hm
      interval_cases m
      revert hprime
      decide⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (3 ^ 3 + m ^ 3 + 1).Prime} 1 :=
    ⟨⟨le_rfl, by decide⟩, fun m hm => hm.1⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (4 ^ 3 + m ^ 3 + 1).Prime} 2 :=
    ⟨⟨by decide, by decide⟩, fun m hm => by
      by_contra hc
      have hm1 : 1 ≤ m := hm.1
      have hm2 : m < 2 := not_le.mp hc
      obtain ⟨_, hprime⟩ := hm
      interval_cases m
      revert hprime
      decide⟩
  exact h.csInf_eq

/--
"Exponent $k > 2$: Are there infinitely many primes of the forms $n^k + 
    m^k$ and $n^k + m^k + 1^k$?"-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) (hk : 3 ≤ k) :
    Set.Infinite {p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ p.Prime ∧ p = n ^ k + m ^ k + 1} := by
  sorry

end OeisA159829
