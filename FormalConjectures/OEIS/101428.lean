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
# Number of ways to write n as an ordered sum of a triangular number (A000217) and a square (A000290)

a(n) is the number of ways to write $n$ as an ordered sum of a triangular number and a square.

*References:* [A101428](https://oeis.org/A101428)
-/

namespace OeisA101428

/-- The $k$-th triangular number $T_k = k(k+1)/2$. -/
def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

/-- The primary defining sequence `a`.
a(n) is the number of ways to write $n$ as an ordered sum of a triangular number (A000217) and a square (A000290).
$$a(n) = \# \left\{ (k, m) \in \mathbb{N}^2 \mid \frac{k(k+1)}{2} + m^2 = n \right\}$$ -/
def a (n : ℕ) : ℕ :=
  let S := (Finset.range (n + 1)).product (Finset.range (n + 1))
  Finset.card (Finset.filter (fun p : ℕ × ℕ => triangular p.fst + p.snd^2 = n) S)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 2 := by rfl

@[category test, AMS 11]
lemma test_a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_3 : a 3 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_4 : a 4 = 2 := by rfl

end OeisA101428
