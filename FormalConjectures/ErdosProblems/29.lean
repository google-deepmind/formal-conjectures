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
# Erdős Problem 29

*References:*
- [erdosproblems.com/29](https://www.erdosproblems.com/29)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er89d] Erdős, P., *Some old and new problems on additive and combinatorial number theory*.
  Combinatorial Mathematics: Proceedings of the Third International Conference (New York, 1985)
  (1989), 181-186.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [JPSZ24] Jain, V. and Pham, H. T. and Sawhney, M. and Zakharov, D., *An explicit economical
  additive basis*. arXiv:2405.08650 (2024).
-/

@[expose] public section

open Filter Asymptotics AdditiveCombinatorics
open scoped Pointwise

namespace Erdos29

/--
Is there an explicit construction of a set $A\subseteq \mathbb{N}$ such that $A+A=\mathbb{N}$ but
$1_A\ast 1_A(n)=o(n^\epsilon)$ for every $\epsilon>0$?

The existence of such a set was asked by Sidon to Erdős in 1932. Erdős (eventually) proved the
existence of such a set using probabilistic methods. This problem asks for a constructive
solution. An explicit construction was given by Jain, Pham, Sawhney, and Zakharov [JPSZ24].

The formal statement records the existence of such a set; the linked formal proof exhibits an
explicit construction.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos29.lean#L104"]
theorem erdos_29 : answer(True) ↔ ∃ A : Set ℕ, A + A = Set.univ ∧ ∀ ε : ℝ, 0 < ε →
    (fun n : ℕ => (sumRep A n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ ε := by
  sorry

end Erdos29
