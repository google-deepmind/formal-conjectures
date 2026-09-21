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
# Erdős Problem 341

*References:*
* [erdosproblems.com/341](https://www.erdosproblems.com/341)
* [Ben Green's Open Problem 7](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.1)
* [Li26] Li, Z., *Counterexamples to Erdős Problem 341* (2026),
  https://github.com/LiAlreadyExists/Erdos-341/blob/main/paper/Erdos341.pdf
-/

@[expose] public section

open Nat Set Filter
open scoped Topology

namespace Erdos341

/--
Let $A=\{a_1 < \cdots < a_k\}$ be a finite set of integers and extend it to an infinite
sequence $\overline{A}=\{a_1 < a_2 < \cdots \}$ by defining $a_{n+1}$ for $n \geq k$ to be
the least integer exceeding $a_n$ which is not of the form $a_i + a_j$ with $i,j \leq n$.
Is it true that the sequence of differences $a_{m+1}-a_m$ is eventually periodic?

This problem is discussed under Problem 7 on Green's open problems list.

The answer is no: Li [Li26] (with GPT-5.6 Sol) showed that the greedy extension of the seed set
$A = \{1, 2, 3, 5, 7, 13, 22, 27, 28, 32, 36, 40, 47, 48, 52, 63, 71, 77, 81, 89, 97\}$ has a
sequence of differences that is not eventually periodic. The linked formal proof
exhibits such a sequence `a : ℕ → ℕ` (strictly increasing, with the greedy rule holding from
some index on, and with `n ↦ a (n + 1) - a n` not eventually periodic); casting it to `ℤ`
gives a counterexample to the statement below.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos341.lean#L12"]
theorem erdos_341 :
    answer(False) ↔
      ∀ (a : ℕ → ℤ),
        (∀ᶠ n in atTop,
          IsLeast { x | a n < x ∧ x ∉ { a i + a j | (i ≤ n) (j ≤ n) } } (a (n + 1))) →
        let d := fun i ↦ a (i + 1) - a i
        ∃ p > 0, ∀ᶠ m in atTop, d (m + p) = d m := by
  sorry

end Erdos341
