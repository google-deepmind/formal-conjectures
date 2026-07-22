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
# Numerator of Sum_{k=1..n} 2^k/k.

Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2) if and only if n is prime.

*References:*
- [A108866](https://oeis.org/A108866)
-/

namespace OeisA108866

/--
The primary defining sequence `a`.
a n is the numerator of $\sum_{k=1}^n \frac{2^k}{k}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range n) fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)).num.natAbs

local macro "eval_a" : tactic => `(tactic| (delta a; norm_num))

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 2 := by eval_a

@[category test, AMS 11]
lemma test_a_2 : a 2 = 4 := by eval_a

@[category test, AMS 11]
lemma test_a_3 : a 3 = 20 := by eval_a

@[category test, AMS 11]
lemma test_a_4 : a 4 = 32 := by eval_a

/--
The rational number inside the numerator function in the conjecture.
$$ -\frac{2}{n} + \sum_{k=1}^n \frac{2^k}{k} $$
-/
noncomputable def rat_expression (n : ℕ) : Rat :=
  if n > 0 then
    (-2 : Rat) / (n : Rat) + Finset.sum (Finset.range n) fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)
  else
    0

/--
Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2) if and only if n is prime.
-/
@[category research open, AMS 11]
theorem main_conjecture {n : ℕ} (hn : n > 3) :
    (rat_expression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ Nat.Prime n := by
  sorry

end OeisA108866
