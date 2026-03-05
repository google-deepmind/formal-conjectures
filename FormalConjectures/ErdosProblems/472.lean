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

/-!
# Erdős Problem 472

*Reference:* [erdosproblems.com/472](https://www.erdosproblems.com/472)

Given some initial finite sequence of primes $q_1 < \cdots < q_m$, extend it so that
$q_{n+1}$ is the smallest prime of the form $q_n + q_i - 1$ for $n \geq m$. Is there an
initial starting sequence so that the resulting sequence is infinite?

A problem due to Ulam. For example if we begin with $3, 5$ then the sequence
continues $3, 5, 7, 11, 13, 17, \ldots$. It is possible that this sequence is infinite.
-/

namespace Erdos472

/-- A sequence $q : \mathbb{N} \to \mathbb{N}$ is an Erdős-Ulam sequence (Problem 472) with initial
    segment of length $m$ if all terms are prime and for each $n$ with $n + 1 \geq m$,
    $q(n + 1)$ is the smallest prime of the form $q(n) + q(i) - 1$ for $i \leq n$. -/
def IsErdos472Sequence (q : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ n, Nat.Prime (q n)) ∧
  StrictMono q ∧
  ∀ n, m ≤ n + 1 →
    (∃ i, i ≤ n ∧ q (n + 1) = q n + q i - 1) ∧
    (∀ i, i ≤ n → Nat.Prime (q n + q i - 1) → q (n + 1) ≤ q n + q i - 1)

/--
Erdős Problem 472 (Open):
There exists an initial finite sequence of primes such that the Erdős-Ulam
extension process produces an infinite sequence. That is, there exists an
infinite sequence where each term after the initial segment is the smallest
prime of the form $q(n) + q(i) - 1$.
-/
@[category research open, AMS 11]
theorem erdos_472 : answer(sorry) ↔
    ∃ (q : ℕ → ℕ) (m : ℕ), 0 < m ∧ IsErdos472Sequence q m := by
  sorry

end Erdos472
