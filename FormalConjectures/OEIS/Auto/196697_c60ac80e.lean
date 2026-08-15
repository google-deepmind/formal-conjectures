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

open Nat Finset

/--
A196697: Number of primes of the form of $2^n \pm 2^k \pm 1$ with $0 \le k < n$.
-/
def a (n : ℕ) : ℕ :=
  let candidates_set : Finset ℕ :=
    (range n).biUnion fun k =>
      let p2n := 2^n
      let p2k := 2^k
      -- The four forms are $2^n \pm 2^k \pm 1$ and the negative sign is part of the constant
      insert (p2n + p2k + 1) $ insert (p2n + p2k - 1) $
      insert (p2n - p2k + 1) $ {p2n - p2k - 1}

  -- Filter the set of distinct candidates for primality and return the cardinality.
  (candidates_set.filter Nat.Prime).card

/-- Conjecture: all terms of this sequence are greater than 0. -/
theorem oeis_196697_conjecture_0 :
  ∀ n : ℕ, 1 ≤ n → a n > 0 :=
by sorry
