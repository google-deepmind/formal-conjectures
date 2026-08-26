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
# Erdős Problem 1209

*References:*
- [erdosproblems.com/429](https://www.erdosproblems.com/429)
- [erdosproblems.com/1102](https://www.erdosproblems.com/1102)
- [erdosproblems.com/1209](https://www.erdosproblems.com/1209)
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115.
-/

open Nat Set

namespace Erdos1209

/--
Let $A=\{a_1<a_2<\cdots\}$ be a sequence of integers which tends to infinity sufficiently fast.
If there is an $n$ such that all $n+a_k$ are primes then must there exist infinitely many such $n$?

Erdős [Er80] wrote 'unless I overlook a trivial way of getting a counterexample these questions
are quite hopeless'. There is indeed a trivial counterexample (a variant of the construction in
[erdosproblems.com/429]): define $a_1=2$ and for $k\geq 2$ let $a_k>a_{k-1}$ be a prime such that
$a_k+k\equiv 0\pmod{q_k}$, where $q_k$ is some prime not dividing $k$. This sequence can be made to
grow arbitrarily fast

See also [erdosproblems.com/429] and [erdosproblems.com/1102].
-/
@[category research solved, AMS 11]
theorem erdos_1209.parts.i :
    answer(False) ↔
      ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
        (∃ n, ∀ k, (n + a k).Prime) →
        {n | ∀ k, (n + a k).Prime}.Infinite := by
  sorry

/--
What if we ask for $n+a_k$ to be squarefree instead of prime?

A similar construction provides a counterexample to the squarefree question.
-/
@[category research solved, AMS 11]
theorem erdos_1209.parts.ii :
    answer(False) ↔
      ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
        (∃ n, ∀ k, Squarefree (n + a k)) →
        {n | ∀ k, Squarefree (n + a k)}.Infinite := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is always a prime?

ebarschkis and GPT have proved that there are no $n$ such that $n+2^{2^k}$ is always prime: let
$n\geq 3$ be any odd integer. If $k$ is chosen sufficiently large, and $p=n+2^{2^{k}}$ is prime,
then the multiplicative order of $2^{2^k}\pmod{p}$, say $m$ is odd, and hence if $l$ is chosen such
that $2^l\equiv 1\pmod{m}$ then $p\mid n+2^{2^{k+rl}}$ for all $r\geq 1$.

This was formalized in Lean by Barschkis using ChatGPT.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/ebarschkis/ErdosProblem/blob/main/Problem1209/Formalization.lean"]
theorem erdos_1209.parts.iii.a :
    answer(False) ↔ ∃ n : ℕ, ∀ k : ℕ, (n + 2 ^ (2 ^ k)).Prime := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is always squarefree?
-/
@[category research open, AMS 11]
theorem erdos_1209.parts.iii.b :
    answer(sorry) ↔ ∃ n : ℕ, ∀ k : ℕ, Squarefree (n + 2 ^ (2 ^ k)) := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is infinitely often a prime?
-/
@[category research open, AMS 11]
theorem erdos_1209.parts.iii.c :
    answer(sorry) ↔ ∃ n : ℕ, {k | (n + 2 ^ (2 ^ k)).Prime}.Infinite := by
  sorry

/--
Are there $n$ such that $n+2^{2^k}$ is infinitely often squarefree?
-/
@[category research open, AMS 11]
theorem erdos_1209.parts.iii.d :
    answer(sorry) ↔ ∃ n : ℕ, {k | Squarefree (n + 2 ^ (2 ^ k))}.Infinite := by
  sorry

end Erdos1209
