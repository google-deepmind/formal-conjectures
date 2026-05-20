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

open Nat BigOperators

/--
The numerator product $\prod_{i=1}^{n} (3n+i-1)! \cdot (i-1)!$ for the sequence A352656.
-/
def A352656_num_prod (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun i =>
    (3 * n + i - 1).factorial * (i - 1).factorial

/--
The denominator product $\prod_{i=1}^{n} (2n+i-1)! \cdot (n+i-1)!$ for the sequence A352656.
-/
def A352656_den_prod (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun i =>
    (2 * n + i - 1).factorial * (n + i - 1).factorial

/--
A352656: The number of lozenge tilings of a semiregular hexagon of side lengths $n, n, 2n, n, n$ and $2n$;
equivalently, the number of plane partitions whose solid Young diagram fits inside an $n \times n \times 2n$ box.
The formula used is:
$$a(n) = \prod_{i=1}^{n} \frac{(3n+i-1)! \cdot (i-1)!}{(2n+i-1)! \cdot (n+i-1)!}$$
-/
def A352656 (n : ℕ) : ℕ :=
  if n = 0 then
    1 -- a(0) = 1
  else
    A352656_num_prod n / A352656_den_prod n


theorem a_zero : A352656 0 = 1 := by simp [A352656]

theorem a_one : A352656 1 = 3 := by sorry

theorem a_two : A352656 2 = 105 := by sorry

theorem a_three : A352656 3 = 41580 := by sorry

/--
The superfactorial function S(n) = Product_{k = 0..n-1} k! with S(0) = 1.
-/
def superfactorial (n : ℕ) : ℕ :=
  (Finset.range n).prod fun k => k.factorial

/--
The superfactorial ratio $F(a, b, c) := \frac{S(a) S(b) S(c) S(a+b+c)}{S(a+b) S(a+c) S(b+c)}$.
This is known to be an integer, which justifies the use of ℕ division.
-/
def F (a b c : ℕ) : ℕ :=
  let num := superfactorial a * superfactorial b * superfactorial c * superfactorial (a + b + c)
  let den := superfactorial (a + b) * superfactorial (a + c) * superfactorial (b + c)
  num / den

/--
%C A352656 Conjecture 1: the supercongruences F(a*p^r,b*p^r,c*p^r) == F(a*p^(r-1),b*p^(r-1),c*p^(r-1))^p (mod p^(4*r))
hold for all primes p, where r is a positive integer and a, b and c are nonnegative integers.
(We interpret the undefined 'k' in the original OEIS entry as 'r').
-/
theorem oeis_A352656_conjecture_1 (p : ℕ) (hp : p.Prime) (r : ℕ) (hr : 0 < r) (a b c : ℕ) :
  (F (a * p ^ r) (b * p ^ r) (c * p ^ r) : ℤ) ≡
  (F (a * p ^ (r - 1)) (b * p ^ (r - 1)) (c * p ^ (r - 1)) : ℤ) ^ p
    [ZMOD (p ^ (4 * r) : ℤ)] :=
by sorry
