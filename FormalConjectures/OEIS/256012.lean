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
# Conjectures associated with a

a: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that
$\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.

*References:*
- [A256012](https://oeis.org/A256012)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA256012


open Nat Finset

/--
a: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that
$\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.
-/
def a (n : ℕ) : ℕ :=
  -- The parts must be $\le n$ to sum to $n$.
  -- This is $\{1, 2, \dots, n\}$
  let potential_parts : Finset ℕ := range (n + 1) \ {0}

  -- We count all subsets P of potential_parts that satisfy the sum and the property.
  card <| filter (fun P : Finset ℕ =>
    P.sum id = n ∧
    (∀ k ∈ P, ¬ Squarefree k)
  ) (powerset potential_parts)


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by decide

@[category test, AMS 11]
lemma a_one : a 1 = 0 := by native_decide

@[category test, AMS 11]
lemma a_two : a 2 = 0 := by native_decide

@[category test, AMS 11]
lemma a_three : a 3 = 0 := by native_decide

@[category test, AMS 11]
lemma a_four : a 4 = 1 := by native_decide


/--
a: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that
$\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/256012.wip.lean#L91"]
theorem target_theorem_0
  (n : ℕ) (hn : n > 23) : a n > 0 := by
    sorry

end OeisA256012
