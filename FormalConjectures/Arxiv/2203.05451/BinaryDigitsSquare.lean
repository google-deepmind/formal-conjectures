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
# Equal binary digit sums of an odd integer and its square

Let $s_2(n)$ denote the sum of the binary digits of $n$. Hare, Laishram, and Stoll proved that the
set of odd positive integers $n$ satisfying $s_2(n) = s_2(n^2) = k$ is finite for $1 \le k \le 8$
and infinite for $k \in \{12, 13\} \cup [16, \infty)$. Aloui, Jamet, Kaneko, Kopecki, Popoli, and
Stoll subsequently proved finiteness for $k \in \{9, 10, 11\}$, leaving only $k \in \{14, 15\}$
open as their Conjecture 1.

*References:*
- [Aloui et al., *On the binary digits of $n$ and $n^2$*](https://arxiv.org/abs/2203.05451)
- [Hare, Laishram, and Stoll, *The sum of digits of $n$ and $n^2$*](https://arxiv.org/abs/1001.4170)
-/

@[expose] public section

namespace Arxiv.«2203.05451»

/-- Odd natural numbers $n$ whose binary digit sum equals $k$ both before and after squaring. -/
def equalBinarySquareWeight (k : ℕ) : Set ℕ :=
  {n : ℕ | Odd n ∧ (Nat.digits 2 n).sum = k ∧ (Nat.digits 2 (n ^ 2)).sum = k}

@[category test, AMS 11]
theorem one_mem_weight_one : 1 ∈ equalBinarySquareWeight 1 := by
  simp [equalBinarySquareWeight]

@[category test, AMS 11]
theorem three_mem_weight_two : 3 ∈ equalBinarySquareWeight 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Conjecture 1 (Aloui et al., 2023):** For $k \in \{14, 15\}$, only finitely many odd natural
numbers $n$ satisfy $s_2(n) = s_2(n^2) = k$. -/
@[category research open, AMS 11]
theorem conjecture_one (k : ℕ) (hk : k = 14 ∨ k = 15) :
    (equalBinarySquareWeight k).Finite := by
  sorry

end Arxiv.«2203.05451»
