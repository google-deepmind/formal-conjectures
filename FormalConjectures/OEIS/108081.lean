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
# Number of words in a specific set

The sequence `a` is defined as $a(n) = \sum_{k=0}^n \binom{n+k-1}{k} F(n-k+1)$, where $F(m)$ is the $m$-th Fibonacci number. We formalize a conjecture about the number of words of length $n$ in a set $X$ being related to this sequence.

*References:*
- [A108081](https://oeis.org/A108081)
-/

namespace OeisA108081

open Nat

/-- The primary defining sequence `a`.
$a(n) = \sum_{k=0}^n \binom{n+k-1}{k} F(n-k+1)$, where $F(m)$ is the $m$-th Fibonacci number. -/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (n + k - 1).choose k * fib (n - k + 1)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 5]
lemma test_a_0 : a 0 = 1 := by decide

@[category test, AMS 5]
lemma test_a_1 : a 1 = 2 := by decide

@[category test, AMS 5]
lemma test_a_2 : a 2 = 7 := by decide

@[category test, AMS 5]
lemma test_a_3 : a 3 = 25 := by decide

@[category test, AMS 5]
lemma test_a_4 : a 4 = 92 := by decide

/-- Words are finite sequences of integers. -/
abbrev Word := List ℤ

/-- `l w` is the word obtained by reversing `w` and subtracting 1 from every term. -/
def l (w : Word) : Word :=
  w.reverse.map (fun x => x - 1)

/-- `r w` is the word obtained by reversing `w` and adding 1 to every term. -/
def r (w : Word) : Word :=
  w.reverse.map (fun x => x + 1)

/-- `x_word` is the smallest set of words satisfying the inductive properties described in A108081. -/
inductive x_word : Word → Prop
  | base : x_word [0]
  | step_left {u v : Word} (hu : x_word u) (hv : x_word v) : x_word (l u ++ v)
  | step_right {u v : Word} (hu : x_word u) (hv : x_word v) : x_word (u ++ r v)

/-- `x_n n` is the set of words in `x_word` of length `n`. -/
def x_n (n : ℕ) : Set Word :=
  {w : Word | x_word w ∧ w.length = n}

/--
"The number of words of length n for n<=12 is given by a(n+1). Is this always true?"

Formalized as $|X_n| = a(n-1)$ for $n \ge 1$, because the sequence values $a(0)=1, a(1)=2, a(2)=7$
match the examples given for word lengths $n=1, 2, 3$ respectively.
-/
@[category research open, AMS 5]
theorem count_words_in_x_is_a_shifted (n : ℕ) :
    n ≥ 1 → Set.ncard (x_n n) = a (n - 1) := by
  sorry

end OeisA108081
