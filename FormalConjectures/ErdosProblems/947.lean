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
# Erdős Problem 947

*References:*
- [erdosproblems.com/947](https://www.erdosproblems.com/947)
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*. Number theory
  day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [Er50] Erdős, P., *On integers of the form $2^k+p$ and some related problems*. Summa Brasil.
  Math. (1950), 113-123.
-/

@[expose] public section

open Function

namespace Erdos947

/--
There is no exact covering system - that is, a finite collection of congruence classes
$a_i\pmod{n_i}$ with distinct $n_i$ such that every integer satisfies exactly one of these
congruence classes.

This is true, and was proved independently by Mirsky and Newman and by Davenport and Rado; the
Mirsky–Newman proof first appeared in [Er50]. See also [Er77c].

A `StrictCoveringSystem ℤ` is a finite family of congruence classes with distinct moduli
$n_i \geq 2$ covering $\mathbb{Z}$; the trivial exact covering system consisting of the single
class $0 \pmod 1$ is therefore excluded.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos947.lean#L277"]
theorem erdos_947 : ¬ ∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset) := by
  sorry

end Erdos947
