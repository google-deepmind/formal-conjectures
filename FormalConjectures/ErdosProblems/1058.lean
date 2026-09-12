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
# Erdős Problem 1058

*Reference:* [erdosproblems.com/1058](https://www.erdosproblems.com/1058)
-/

namespace Erdos1058

/-- The $k$th prime, with $p_1=2$. -/
noncomputable def p (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- `n` lies in $[p_{k-1}, p_k)$ and the only prime divisors of $n!+1$ are $p_k$ and $p_{k+1}$. -/
def Special (n : ℕ) : Prop :=
  ∃ k ≥ 2, n ∈ Set.Ico (p (k - 1)) (p k) ∧
    ∀ q : ℕ, q.Prime → q ∣ n.factorial + 1 → q = p k ∨ q = p (k + 1)

/--
Let $2=p_1<p_2<\cdots$ be the sequence of prime numbers. Are there only finitely many $n$ such that
$n\in [p_{k-1},p_k)$ and the only primes dividing $n!+1$ are $p_{k}$ and $p_{k+1}$?
-/
@[category research open, AMS 11]
theorem erdos_1058 : answer(sorry) ↔ { n : ℕ | Special n }.Finite := by
  sorry

end Erdos1058
