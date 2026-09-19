/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1058

*References:*
- [erdosproblems.com/1058](https://www.erdosproblems.com/1058)
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
- [Lu01] Luca, Florian, *On a conjecture of Erdős and Stewart*. Math. Comp. (2001), 893-896.
-/

@[expose] public section

open Nat

namespace Erdos1058

/--
`n` is a *solution* if `n ∈ [p_{k-1}, p_k)` for some `k` (with the convention `p_0 = 1`, where
`p_1 = 2 < p_2 < ⋯` are the primes) and the only primes dividing `n! + 1` are `p_k` and
`p_{k+1}`. Primes are indexed from `0` by `Nat.nth Nat.Prime`.
-/
def IsSolution (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, (if k = 0 then 1 else nth Nat.Prime (k - 1)) ≤ n ∧
    n < nth Nat.Prime k ∧
      ∀ r : ℕ, r.Prime → r ∣ n ! + 1 → r = nth Nat.Prime k ∨ r = nth Nat.Prime (k + 1)

/--
Let $2=p_1<p_2<\cdots$ be the sequence of prime numbers. Are there only finitely many $n$ such
that $n\in [p_{k-1},p_k)$ and the only primes dividing $n!+1$ are $p_{k}$ and $p_{k+1}$?

A conjecture of Erdős and Stewart, as reported in problem A2 of Guy's collection [Gu04]. The only
known cases are $n=1,2,3,4,5$. Luca [Lu01] proved that indeed these are the only solutions.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1058.lean#L47"]
theorem erdos_1058 : answer(True) ↔ {n | IsSolution n}.Finite := by
  sorry

/-- Luca [Lu01] proved that $n = 1, 2, 3, 4, 5$ are the only solutions. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1058.lean#L47"]
theorem erdos_1058.variants.luca : {n | IsSolution n} = {1, 2, 3, 4, 5} := by
  sorry

end Erdos1058
