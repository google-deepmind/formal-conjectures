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
# Erdős Problem 1198

*References:*
- [erdosproblems.com/1198](https://www.erdosproblems.com/1198)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Hi74] Hindman, Neil, *Finite sums from sequences within cells of a partition of $\mathbb{N}$*.
  J. Combinatorial Theory Ser. A (1974), 1-11.
- [Sm95] Smith, Gregory L., *Partitions and ($m$ and $n$) sums of products*. J. Combin. Theory
  Ser. A (1995), 77-94.
-/

@[expose] public section

open Finset

namespace Erdos1198

/--
If $\mathbb{N}$ is $2$-coloured, must there exist an infinite set $A=\{a_1<a_2<\cdots\}$ such that
all expressions of the shape
$$\sum_{j=1}^{k}\prod_{i\in S_j}a_i,$$
for $k\geq 1$ and pairwise disjoint nonempty finite sets of indices $S_1,\ldots,S_k$ (excluding the
trivial expressions $a_i$, that is $k=1$ and $|S_1|=1$), have the same colour?

Erdős [Er80, p.104] wrote that "one would perhaps guess that the answer must be 'no' but no
counterexample is in sight". The case where every $S_j$ is a singleton is Hindman's theorem [Hi74].
The answer is no: a counterexample was given by Smith [Sm95].
-/
@[category research solved, question, AMS 5 11]
theorem erdos_1198 :
    ¬ ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
      ∀ (k : ℕ) (S : Fin k → Finset ℕ), 0 < k → (∀ j, (S j).Nonempty) →
        Pairwise (fun j j' => Disjoint (S j) (S j')) → ¬ (k = 1 ∧ ∀ j, #(S j) = 1) →
        c (∑ j, ∏ i ∈ S j, a i) = col := by
  sorry

/--
The case where every $S_j$ is a singleton (Hindman's theorem [Hi74]): for every $2$-colouring of
$\mathbb{N}$ there is an infinite set all of whose finite sums of distinct elements have the same
colour.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/linrock/math-proofs/blob/410fa9071d430791d9342617e35eeb94da78bbc8/erdos-1198/Proofs/HindmanBlockConstruction1198.lean#L177"]
theorem erdos_1198.variants.hindman :
    ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
      ∀ T : Finset ℕ, T.Nonempty → c (∑ i ∈ T, a i) = col := by
  sorry

end Erdos1198
