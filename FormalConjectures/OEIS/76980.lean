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
module

public import FormalConjecturesUtil


/-!
# Conjecture from Zhi-Wei Sun

*References:*
- [A076980](https://oeis.org/A076980).
-/

@[expose] public section

namespace OeisA76980

/--
`m` is a Leyland number if $m = 3$ or $m = n^k + k^n$ for natural numbers $n, k > 1$.
-/
def IsLeyland (m : ℕ) : Prop :=
  m = 3 ∨ ∃ n > 1, ∃ k > 1, m = n ^ k + k ^ n

/--
The sequence of Leyland numbers `a`.
`a n` is the $n$-th Leyland number in increasing order.

Note: `a 0 = 3`, so `a n` is OEIS's $a(n+1)$.
-/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsLeyland n

@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by
  unfold a
  rw [Nat.nth_zero, IsLeast.csInf_eq]
  have h3 : IsLeyland 3 := Or.inl rfl
  have hge : ∀ m, IsLeyland m → 3 ≤ m := by
    intro m hm
    by_cases h : 3 ≤ m
    · assumption
    · unfold IsLeyland at hm
      obtain _ | h' := hm
      · omega
      · obtain ⟨n, hn, k, hk, hmk⟩ := h'
        have : n ≤ n ^ k :=  Nat.le_self_pow (by positivity) n
        have : k ^ n > 0 := by positivity
        omega
  exact ⟨h3, hge⟩

/--
First statement of the conjecture from Zhi-Wei Sun:
(i) For each $n > 0$, we have $a(n) \le p+1 < a(n+1)$ for some prime $p$.
-/
@[category research open, AMS 11]
theorem conjecture_i (n : ℕ) : ∃ p : ℕ, p.Prime ∧ a n ≤ p + 1 ∧ p + 1 < a (n + 1) := by
  sorry

/--
Second statement of the conjecture from Zhi-Wei Sun:
(ii) $a(n) < p < a(n+1)$ for some prime $p$, except that the interval $(a(5), a(6)) = (54, 57)$ contains no prime.
-/
@[category research open, AMS 11]
theorem conjecture_ii (n : ℕ) (hn : n ≠ 4) : ∃ p : ℕ, p.Prime ∧ a n < p ∧ p < a (n + 1) := by
  sorry

end OeisA76980
