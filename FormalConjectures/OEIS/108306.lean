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
# A108306: Expansion of (3x+1)/(1-3x-3x^2)

Expansion of $$(3x+1)/(1-3x-3x^2).$$ This sequence satisfies the linear recurrence relation $a(0)=1$, $a(1)=6$, and $a(n) = 3a(n-1) + 3a(n-2)$ for $n \ge 2$.

*References:*
- [A108306](https://oeis.org/A108306)
-/

namespace OeisA108306

/-- The primary defining sequence `a`.
`a n` is the $n$-th term of the expansion of $(3x+1)/(1-3x-3x^2)$, satisfying $a(0)=1, a(1)=6, a(n)=3a(n-1)+3a(n-2)$. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | k + 2 => 3 * a (k + 1) + 3 * a k

@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 6 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 21 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 81 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 306 := by decide

open Matrix

/--
The matrix for the specific case $a=5, b=2$.
$$M = \begin{pmatrix} 1 & 5 \\ 1 & 2 \end{pmatrix}$$
-/
def m : Matrix (Fin 2) (Fin 2) ℕ :=
  fun i j => match i, j with
  | 0, 0 => 1
  | 0, 1 => 5
  | 1, 0 => 1
  | 1, 1 => 2

/--
The sequence is the INVERT transform of (1, 5, 10, 20, 40, 80, 160, ...) and can be obtained by extracting the upper left terms of matrix powers of [(1,5); (1,2)].
These results are a case (a=5, b=2) of the general conjecture below.
-/
@[category textbook, AMS 11]
theorem a_is_invert_transform_case (n : ℕ) :
    a n = (m ^ (n + 1)) 0 0 := by
  sorry

/-- The c sequence for the general INVERT transform conjecture. c(1)=1, c(k)=a*b^(k-2) for k>=2. -/
def invert_seq_c (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (k + 2) => a * b^k

/-- The INVERT transform of the sequence c. -/
noncomputable def invert_seq_d (a b : ℕ) (n : ℕ) : ℕ :=
  Nat.strongRecOn n
    (fun m ih =>
      if m = 0 then 1
      else Finset.sum (Finset.range m) (fun i =>
        if h : i < m then invert_seq_c a b (m - i) * ih i h else 0))

/-- The general 2x2 matrix [(1,a); (1,b)]. -/
def gen_matrix (a b : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  fun i j => match i, j with
  | 0, 0 => 1
  | 0, 1 => a
  | 1, 0 => 1
  | 1, 1 => b

/--
The conjecture: The INVERT transform of a sequence starting (1, a, a*b, a*b^2, a*b^3, ...) is equivalent to extracting the upper left terms of powers of the 2x2 matrix [(1,a); (1,b)].
-/
@[category research open, AMS 11]
theorem main_conjecture (a_val b_val n : ℕ) :
    invert_seq_d a_val b_val n = (gen_matrix a_val b_val ^ n) 0 0 := by
  sorry

end OeisA108306
