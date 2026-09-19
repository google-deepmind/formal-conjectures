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
# Number of $0 < k < n-2$ with $p = \phi(k) + \phi(n-k)/2 + 1$ and $p_p - p \pm 1$ prime

Let $\phi$ denote Euler's totient function and $p_m$ denote the $m$-th prime number.
The sequence $a(n)$ counts the number of integers $0 < k < n - 2$ such that
$p = \phi(k) + \phi(n-k)/2 + 1$, $p_p - p - 1$, and $p_p - p + 1$ are all prime.

*References:*
- [A236097](https://oeis.org/A236097)
-/

namespace OeisA236097

/-- $a(n)$ is the number of integers $0 < k < n-2$ such that $p = \phi(k) + \phi(n-k)/2 + 1$,
$\operatorname{prime}(p) - p - 1$, and $\operatorname{prime}(p) - p + 1$ are all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 (n - 2),
    let p := k.totient + (n - k).totient / 2 + 1
    let pPrime := Nat.nth Nat.Prime (p - 1)
    if p.Prime ∧ (pPrime - p - 1).Prime ∧ (pPrime - p + 1).Prime then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  unfold a
  have h : Finset.Ico 1 2 = {1} := by decide
  rw [h, Finset.sum_singleton]
  have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  dsimp only
  change (if (Nat.totient 1 + Nat.totient 3 / 2 + 1).Prime ∧
      (Nat.nth Nat.Prime (Nat.totient 1 + Nat.totient 3 / 2 + 1 - 1) -
        (Nat.totient 1 + Nat.totient 3 / 2 + 1) - 1).Prime ∧
      (Nat.nth Nat.Prime (Nat.totient 1 + Nat.totient 3 / 2 + 1 - 1) -
        (Nat.totient 1 + Nat.totient 3 / 2 + 1) + 1).Prime then 1 else 0) = 0
  have ht : Nat.totient 1 + Nat.totient 3 / 2 + 1 = 3 := by decide
  rw [ht, show (3 - 1 : ℕ) = 2 by rfl, h2]
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  unfold a
  have h : Finset.Ico 1 3 = {1, 2} := by decide
  rw [h, Finset.sum_pair (by decide)]
  have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have ht1 : Nat.totient 1 + Nat.totient (5 - 1) / 2 + 1 = 3 := by decide
  have ht2 : Nat.totient 2 + Nat.totient (5 - 2) / 2 + 1 = 3 := by decide
  dsimp only
  rw [ht1, ht2, show (3 - 1 : ℕ) = 2 by rfl, h2]
  decide

/--
Conjecture: $a(n) > 0$ for all $n > 31$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 31 < n) : 0 < a n := by
  sorry

end OeisA236097
