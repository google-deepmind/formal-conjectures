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
# Determinant of matrix with entries indicating primality of $i^2 + j^2$

The sequence $a(n)$ is the determinant of the $n \times n$ matrix $M$ defined by
$M(i,j) = 1$ if $i^2 + j^2$ is prime, and $0$ otherwise, where $1 \le i, j \le n$.

*References:*
- [A071524](https://oeis.org/A071524)-/

namespace OeisA71524

open Matrix

/-- Determinant of the $n \times n$ matrix with $(i,j)$ entry $1$ if $(i+1)^2 + (j+1)^2$ is prime,
and $0$ otherwise. -/
def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ 2 + j_idx ^ 2).Prime then 1 else 0
  M.det

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  decide +native

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide +native

/-- Determinant of the $n \times n$ matrix with $(i,j)$ entry $1$
if $(i+1)^{2^m} + (j+1)^{2^m}$ is prime, and $0$ otherwise. -/

def generalDet (m n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ (2 ^ m) + j_idx ^ (2 ^ m)).Prime then 1 else 0
  M.det

/--
Conjecture: $a(n) = 0$ for no $n > 28$.
- _Zhi-Wei Sun_, Aug 26 2013
-/
@[category research open, AMS 11 15]
theorem conjecture1 (n : ℕ) (hn : 28 < n) : a n ≠ 0 := by
  sorry

/--
Conjecture (Generalization): For every $m \in \mathbb{N}$, the determinant `generalDet m n` is
nonzero for all sufficiently large $n$.
- _Zhi-Wei Sun_, Aug 26-27 2013
-/
@[category research open, AMS 11 15]
theorem conjecture2 (m : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N < n → generalDet m n ≠ 0 := by
  sorry

end OeisA71524
