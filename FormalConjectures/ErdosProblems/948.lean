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
# Erdős Problem 948

*References:*
- [erdosproblems.com/948](https://www.erdosproblems.com/948)
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [ErGa91] Erdős, P. and Galvin, F., *Some Ramsey-type theorems*. Discrete Math. 87 (1991),
  261–269.
-/

@[expose] public section

namespace Erdos948

/--
Is there a function $f(n)$ and a $k$ such that in any $k$-colouring of the integers there exists a
sequence $a_1 < a_2 < \cdots$ such that $a_n < f(n)$ for infinitely many $n$ and the set
$$\left\{ \sum_{i \in S} a_i : \textrm{finite nonempty } S \right\}$$
does not contain all colours?

A question of Erdős [Er77c] and Erdős and Galvin [ErGa91]. The answer is no: GPT-5.5 Pro (prompted
by Price) showed that for every $f$ there is a colouring of the integers such that the finite sums
of every such sequence use all colours. The linked formal proof (Codex and GPT-5.6 Sol) gives, for
every $f$ and $k \ge 1$, a colouring $c : \mathbb{Z} \to \{0, \ldots, k - 1\}$ such that for every
strictly increasing $a$ with $a_n < f(n)$ infinitely often and every colour, some nonempty finite
sum of the $a_i$ has that colour.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos948.lean#L451"]
theorem erdos_948 : answer(False) ↔
    ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧ ∀ colouring : ℤ → Fin k,
      ∃ a : ℕ → ℤ, StrictMono a ∧ {n | a n < f n}.Infinite ∧
        ∃ c : Fin k, ∀ S : Finset ℕ, S.Nonempty → colouring (∑ i ∈ S, a i) ≠ c := by
  sorry

/--
The original question asks for the set of finite sums to be monochromatic. Galvin showed that
this fails for $k = 2$, and it fails for every $k \ge 2$ by the negative answer to `erdos_948`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos948.lean#L451"]
theorem erdos_948.variants.monochromatic : answer(False) ↔
    ∃ (f : ℕ → ℕ) (k : ℕ), 2 ≤ k ∧ ∀ colouring : ℤ → Fin k,
      ∃ a : ℕ → ℤ, StrictMono a ∧ {n | a n < f n}.Infinite ∧
        ∃ c : Fin k, ∀ S : Finset ℕ, S.Nonempty → colouring (∑ i ∈ S, a i) = c := by
  sorry

end Erdos948
