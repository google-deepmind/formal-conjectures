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
# Erdős Problem 472

*Reference:* [erdosproblems.com/472](https://www.erdosproblems.com/472)
-/

namespace Erdos472

/-- The initial segment $q_0,\ldots,q_{m-1}$ is a strictly increasing sequence of primes. -/
def InitialPrimeSegment (m : ℕ) (q : ℕ → ℕ) : Prop :=
  0 < m ∧
    (∀ i : ℕ, i < m → Nat.Prime (q i)) ∧
      ∀ i j : ℕ, i < j → j < m → q i < q j

/-- The prime $r$ is an eligible next term after $q_{\mathrm{prev}}$. -/
def EligibleNextPrime (q : ℕ → ℕ) (prev t r : ℕ) : Prop :=
  Nat.Prime r ∧
    q prev < r ∧
      ∃ i : ℕ, i < t ∧ r = q prev + q i - 1

/-- After the initial segment, each term is the least eligible next prime. -/
def UlamPrimeExtension (m : ℕ) (q : ℕ → ℕ) : Prop :=
  InitialPrimeSegment m q ∧
    ∀ t : ℕ,
      m ≤ t →
        IsLeast {r : ℕ | EligibleNextPrime q (t - 1) t r} (q t)

/--
Given a finite sequence of primes $q_1<\cdots<q_m$, extend it by taking $q_{n+1}$ to be the
smallest prime of the form $q_n+q_i-1$ for $n\geq m$. Is there an initial sequence for which
this process continues forever?
-/
@[category research open, AMS 11]
theorem erdos_472 : answer(sorry) ↔ ∃ m : ℕ, ∃ q : ℕ → ℕ, UlamPrimeExtension m q := by
  sorry

end Erdos472
