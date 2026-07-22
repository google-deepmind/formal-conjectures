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
# Imaginary part of Product_{k=0..n} (1 + k*i), i = sqrt(-1)

A105751(n) is the imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, where $i = \sqrt{-1}$.

*References:*
- [A105751](https://oeis.org/A105751)
-/

open Complex Filter Topology Nat

namespace OeisA105751

/--
The primary defining sequence `a`.
a n is the imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, where $i = \sqrt{-1}$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_4 : a 4 = -40 := by
  delta a; norm_num [Finset.prod]

/--
Numerical calculation suggests that a similar division holds in this case.
Type 1: primes p that do not divide any element of the sequence {a(n)}.
In this case, unlike in A105750, the set of type 1 primes is empty; that is, every prime p divides some term of this sequence.

Note: The triangular number n*(n+1)/2 divides a(n) (see A164652). In particular, if p is an odd prime then p divides a(p). For p=2, 2 divides a(4)=-40.
-/
@[category textbook, AMS 11]
theorem prime_divides_some_term (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, (p : ℤ) ∣ a n := by
  sorry

/--
Moll's conjecture 5.5 extends to this sequence and takes the form:
(i) the 2-adic valuation v_2(a(n)) ~ n/4 as n -> oo.
-/
@[category research open, AMS 11]
theorem conjecture :
    Tendsto (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (nhds 1) := by
  sorry

/--
Moll's conjecture 5.5 extends to this sequence and takes the form:
(ii) for the other primes of type 2, the p-adic valuation v_p(a(n)) ~ n/(p - 1) as n -> oo.

(Type 2 primes consists of primes p == 1 (mod 4))
-/
@[category research open, AMS 11]
theorem conjecture.variants.moll_p_mod_4_eq_1 {p : ℕ} (hp : p.Prime) (h_mod : p % 4 = 1) :
    Tendsto (fun n ↦ ((p - 1 : ℚ) * (padicValInt p (a n) : ℚ)) / (n : ℚ)) atTop (nhds 1) := by
  sorry

end OeisA105751
