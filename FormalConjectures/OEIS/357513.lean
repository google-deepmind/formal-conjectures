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

open Nat


/-!
Numerator of $sum_{k = 1}^n \frac{1}{k^3} * \binom{n}{k}^2 * \binom{n+k}{k}^2 for $n \ge 1$
with $a(0) = 0$.


*Reference:* [A357513](https://oeis.org/A357513)
-/

namespace OeisA357513

/--
A357513: $a(n) = \text{numerator of }
\sum_{k = 1..n} \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2
\text{ for } n \ge 1 \text{ with } a(0) = 0$.
-/
def a (n : ℕ) : ℕ :=
 ∑ k ∈ (Finset.Icc 1 n), ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) / k ^ 3 |>.num.natAbs


@[category test, AMS 11]
theorem zero : a 0 = 0 := rfl

@[category test, AMS 11]
theorem one : a 1 = 4 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem two : a 2 = 81 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem three : a 3 = 14651 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem four : a 4 = 956875 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

@[category test, AMS 11]
theorem five : a 5 = 1335793103 := by
  unfold a
  norm_num only [Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

/--
We have  $a(p-1) \equiv 0 \pmod{p^4}$ for all primes $p \ge 3$ except $p=7$.

proved by AlphaProof
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/commit/9c7f21e7d4445637538bc1817b058b9b3f31bd2b", AMS 11]
theorem a357513_supercongruence (p : ℕ) (hp : Nat.Prime p) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4] := by
  sorry

/--
Let m be a nonnegative integer and set $u(n) = $$the numerator of
$$\sum{k=1}^{n} \frac{1}{k^{2m+1}} \binom{n}{k}^2 \binom{n+k}{k}^2$$
(seems like a typo in the OEIS entry: the sum starts with $k=0$ there. In order
to avoid a division by zero, we replace start the sum at $k=1$.)
-/
noncomputable def u (m : ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 n),
    ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) / k ^ (2 * m + 1) |>.num.natAbs

/--
We conjecture that $u(p-1) == 0 (mod p^4)$ for all primes $p$,
with a finite number of exceptions that depend on $m$.
-/
@[category research open, AMS 11]
theorem general_supercongruence (m : ℕ) : ∃ (exceptions : Finset ℕ), ∀ p, p.Prime →
    p ∉ exceptions → u m (p - 1) = (0 : ZMod (p ^ 4)) := by
  sorry

@[category test, AMS 11]
theorem general_supercongruence_one_of_a357513_supercongruence :
  type_of% a357513_supercongruence → type_of% (general_supercongruence 1) := by
  intro h
  use {2, 7}
  intro p hp h_exception
  convert h p hp ?_ ?_
  · unfold a u
    zify [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.modEq_zero_iff_dvd, ZMod.natCast_eq_zero_iff]
  · apply hp.two_le.lt_of_ne (by bound)
  · simp_all

end OeisA357513
