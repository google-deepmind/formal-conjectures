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
# Erdős Problem 1187

*References:*
- [erdosproblems.com/1187](https://www.erdosproblems.com/1187)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [GrTa08] Green, Ben and Tao, Terence, *The primes contain arbitrarily long arithmetic
  progressions*. Ann. of Math. (2) (2008), 481-547.
-/

@[expose] public section

namespace Erdos1187

/--
Let $k\geq 3$. Is it true that, in any finite colouring of the integers, there are monochromatic
arithmetic progressions of primes of length $k$?

It follows from the theorem of Green and Tao [GrTa08] (that any set of primes with positive
relative density contains arbitrarily long arithmetic progressions) that the answer to the first
question is yes for any $k\geq 3$.

See also [219](https://www.erdosproblems.com/219).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1187.lean#L246"]
theorem erdos_1187.parts.i : answer(True) ↔ ∀ k : ℕ, 3 ≤ k →
    ∀ (κ : Type) [Finite κ] (c : ℤ → κ), ∃ S : Set ℤ, S.IsAPOfLength k ∧
      (∀ n ∈ S, ∃ p : ℕ, p.Prime ∧ (p : ℤ) = n) ∧
        ∃ γ : κ, ∀ n ∈ S, c n = γ := by
  sorry

/--
Let $k\geq 3$. In any finite colouring of the integers, are there monochromatic arithmetic
progressions of length $k$ whose common difference is a prime?

The answer to the second question is trivially no: colouring the integers by their residue modulo
$4$ creates a colouring in which there is not even any monochromatic pair of integers whose
difference is a prime. Alternatively, one can just use $2$ colours and avoid any $3$-term
progressions whose difference is a prime by colouring $0,1\pmod{4}$ red and $2,3\pmod{4}$ blue.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1187.lean#L246"]
theorem erdos_1187.parts.ii : answer(False) ↔ ∀ k : ℕ, 3 ≤ k →
    ∀ (κ : Type) [Finite κ] (c : ℤ → κ), ∃ (a : ℤ) (p : ℕ) (S : Set ℤ), p.Prime ∧
      S.IsAPOfLengthWith k a p ∧ ∃ γ : κ, ∀ n ∈ S, c n = γ := by
  sorry

end Erdos1187
