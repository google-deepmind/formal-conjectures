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
# Erdős Problem 178

*Reference:* [erdosproblems.com/178](https://www.erdosproblems.com/178)
-/

namespace Erdos178

open Finset BigOperators

/--
Given any infinite collection of infinite strictly increasing sequences of natural
numbers $a_i : \mathbb{N} \to \mathbb{N}$, is there a colouring $f : \mathbb{N} \to \{-1, 1\}$
such that for each $d$ the partial sums $\left|\sum_{j < m} f(a_i\,j)\right|$ are uniformly
bounded over all $m$ and all $i < d$?

The answer is yes (J. Beck, "Balancing Families of Integer Sequences",
Combinatorica, 1981).
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos178.lean"]
theorem erdos_178 (a : ℕ → ℕ → ℕ)
    (ha : ∀ i, StrictMono (a i)) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, ∃ C : ℕ, ∀ m i : ℕ, i < d →
        |∑ j ∈ range m, f (a i j)| ≤ ↑C := by
  sorry

end Erdos178
