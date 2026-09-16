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


*References:*
- [A000945](https://oeis.org/A000945)
- [Mullin63] A. A. Mullin,
  ["Research Problem 8 (ii)"](https://doi.org/10.1090/S0002-9904-1963-11017-4),
  *Bull. Amer. Math. Soc.* **69** (1963), p. 737.
- [Wagstaff93] S. S. Wagstaff, Jr.,
  ["Computing Euclid's primes"](https://oeis.org/A000945/a000945_4.pdf),
  *Bull. Institute Combin. Applications* **8** (1993), pp. 23-32.
- [CrandallPomerance01] R. Crandall and C. Pomerance,
  *Prime Numbers: A Computational Perspective*, Springer (2001), p. 6.
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
"Does the sequence ... contain every prime? ... [It] was considered by Guy and Nowakowski
and later by Shanks, [Wagstaff93] computed the sequence through the 43rd term. The
computational problem inherent in continuing the sequence further is the enormous size of the
numbers that must be factored. Already the number $a(1) \cdots a(43) + 1$ has 180 digits."
- [CrandallPomerance01]

See also [Mullin63].
-/
@[category research open, AMS 11]
theorem every_prime_occurs :
    answer(sorry) ↔ ∀ p, p.Prime → ∃ n ≥ 1, a n = p := by
  sorry

end OeisA945
