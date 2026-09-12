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

import FormalConjecturesUtil

/-!
# $a(n) = \sum_{i=0}^n \binom{2n-i}{n+i}$

Alternatively the sequence `a` can be defined as
$a(n) = \sum_{k=0}^n \binom{n+k-1}{k} F(n-k+1)$, where $F(m)$ is the $m$-th Fibonacci number.
We formalize a conjecture about the number of words of length $n$ in a set $X$ being related
to this sequence.

*References:*
- [A108081](https://oeis.org/A108081)
-/

namespace OeisA108081

open Nat

/-- The primary defining sequence `a`.
$a(n) = \sum_{k=0}^n \binom{n+k-1}{k} F(n-k+1)$, where $F(m)$ is the $m$-th Fibonacci number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n + k - 1).choose k * fib (n - k + 1)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 5]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 5]
theorem a_1 : a 1 = 2 := by decide

@[category test, AMS 5]
theorem a_2 : a 2 = 7 := by decide

@[category test, AMS 5]
theorem a_3 : a 3 = 25 := by decide

@[category test, AMS 5]
theorem a_4 : a 4 = 92 := by decide

/-- Words are finite sequences of integers. -/
abbrev Word := List ℤ

/-- `l w` is the word obtained by reversing `w` and subtracting 1 from every term. -/
def l (w : Word) : Word :=
  w.reverse.map (fun x => x - 1)

/-- `r w` is the word obtained by reversing `w` and adding 1 to every term. -/
def r (w : Word) : Word :=
  w.reverse.map (fun x => x + 1)

/--
`XWord` is the smallest set of words satisfying the inductive properties described in A108081.
-/
inductive XWord : Word → Prop
  | base : XWord [0]
  | step_left {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (l u ++ v)
  | step_right {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (u ++ r v)

/-- `xN n` is the set of words in `XWord` of length `n`. -/
def xN (n : ℕ) : Set Word :=
  {w : Word | XWord w ∧ w.length = n}

/--
"The number of words of length $n$ for $n \le 12$ is given by $a(n+1)$. Is this always true?"

Formalized as $|X_n| = a(n-1)$ for $n \ge 1$, because the sequence values $a(0)=1, a(1)=2, a(2)=7$
match the examples given for word lengths $n=1, 2, 3$ respectively.
-/
@[category research open, AMS 5]
theorem count_words_in_x_is_a_shifted (n : ℕ) :
    n ≥ 1 → Set.ncard (xN n) = a (n - 1) := by
  sorry

end OeisA108081
