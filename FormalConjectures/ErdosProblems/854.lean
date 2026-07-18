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

import FormalConjecturesUtil
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Coprime
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Parity

open scoped Classical
open Finset
open Nat

/-!
# Erdős Problem 854

*Reference:*
 - [erdosproblems.com/854](https://www.erdosproblems.com/854)
-/

namespace Erdos854

/-- The increasing sequence of integers in {1, …, n-1} that are coprime to `n`. -/
noncomputable def coprimeSeq (n : ℕ) : List ℕ :=
  (filter (fun x => coprime x n) (range n)).sort (· ≤ ·)

/-- The set of consecutive differences `a_{i+1} - a_i` for `a = coprimeSeq n`. -/
noncomputable def diffSet (n : ℕ) : Finset ℕ :=
  ((List.zipWith (· - ·) (List.tail (coprimeSeq n)) (coprimeSeq n)).toFinset)

/-- The maximum difference in `diffSet n`.  Returns `0` if the set is empty
(which only happens for `n ≤ 1`). -/
noncomputable def maxDiff (n : ℕ) : ℕ :=
  if h : (diffSet n).Nonempty then (diffSet n).max' h else 0

/-- The set of even differences. -/
noncomputable def evenDiffSet (n : ℕ) : Finset ℕ :=
  (diffSet n).filter (fun d => d % 2 = 0)

/-- The smallest **positive** even integer that does **not** appear in `diffSet n`. -/
noncomputable def smallestMissingEven (n : ℕ) : ℕ :=
  Nat.find (λ d => d > 0 ∧ Even d ∧ d ∉ diffSet n) (by
    -- `diffSet n` is finite, so there are infinitely many positive even integers outside it.
    -- We provide a trivial existence proof (can be filled with a finite argument).
    have h_fin : (diffSet n).Finite := Finset.finite_toSet _
    -- Any sufficiently large even number works; we leave the constructive part as `sorry`.
    sorry)

/-- **Erdős Problem 854**.
Let `n_k` denote the `k`-th primorial (product of the first `k` primes).
Take the increasing sequence of integers coprime to `n_k`:
`1 = a₁ < a₂ < … < a_{φ(n_k)} = n_k - 1`.
Let `D_k` be the set of differences `a_{i+1} - a_i`.

- **Part 1 (estimate the smallest missing even difference).**
  The smallest even integer that does **not** belong to `D_k` grows without bound:
  `∀ C, ∃ k` such that `smallestMissingEven (primorial k) > C`.

- **Part 2 (are there many even differences?).**
  The number of even differences is much larger than the maximum difference.
  Formally, for any constant `C` there exist infinitely many `k` with
  `|D_k ∩ 2ℕ| > C · max D_k`.
-/
@[category research open, AMS 11N25, AMS 11A07]
theorem erdos_854 :
    (∀ C : ℕ, ∃ k : ℕ, smallestMissingEven (Nat.primorial k) > C) ∧
    (∀ C : ℕ, ∃ k : ℕ, (evenDiffSet (Nat.primorial k)).card > C * maxDiff (Nat.primorial k)) :=
by
  sorry

end Erdos854
