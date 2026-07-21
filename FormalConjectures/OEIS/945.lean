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
# Euclid-Mullin sequence

The Euclid-Mullin sequence starts with $a(1) = 2$. Each subsequent term is the smallest prime
factor of one plus the product of all preceding terms. We extend the sequence by $a(0) = 1$ and
write $b(n)$ for the product of the first $n$ official terms.

It is an open problem whether every prime occurs in the sequence.

*References:*
- [A000945](https://oeis.org/A000945)
- A. R. Booker, "A variant of the Euclid-Mullin sequence containing every prime,"
  [arXiv:1605.08929](https://arxiv.org/abs/1605.08929), *Journal of Integer Sequences* **19**
  (2016), Article 16.6.4.
-/

namespace OeisA945

/-- `b n` is the product of the first `n` terms of the Euclid-Mullin sequence. -/
def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => b n * Nat.minFac (b n + 1)

/-- The Euclid-Mullin sequence, extended by `a 0 = 1`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.minFac (b n + 1)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_4 : a 4 = 43 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_5 : a 5 = 13 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_6 : a 6 = 53 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_7 : a 7 = 5 := by norm_num [a, b]

/--
"Does the sequence ... contain every prime?"

See [A000945](https://oeis.org/A000945).
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ p, p.Prime → ∃ n ≥ 1, a n = p := by
  sorry

end OeisA945
