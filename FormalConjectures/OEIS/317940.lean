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
# Nonnegativity of the Dirichlet square root of A046644

A317940 is the integer sequence whose value `a n` is the numerator of the
rational sequence `f n`, where the Dirichlet convolution square of `f` is
A046644. The auxiliary sequence A046644 is multiplicative and takes the value
$2^{\operatorname{A005187}(e)}$ on a prime power $p^e$.

The conjecture asks whether `f n` is nonnegative for every positive `n`.
The proof reduces the problem to prime powers and constructs positive rational
coefficients $c(e)$ satisfying

$$\sum_{i=0}^e c(i)c(e-i)=2^{\operatorname{A005187}(e)}.$$

The coefficients are obtained from formal power series. A positive series
$A$ is defined by the first-order differential equation
$A' = \frac12 D A$. A second explicitly defined series $B$ satisfies
$B' = D B$ and has the same constant term as $A^2$; uniqueness of the
coefficient recurrence therefore gives $A^2=B$. After rescaling the
coefficients by $4^e$, this becomes the displayed prime-power convolution
identity.

Extending $c(e)$ multiplicatively over prime factorizations gives a positive
arithmetic function `root` with `root * root = a046644`. Finally, the recursive
definition of `f` is shown to be the unique Dirichlet square root with value
one at $1$, so `f = root` and every positive-index value of `f` is positive.

This route was found by first exploiting the multiplicativity recorded in the
OEIS entry, reducing the recurrence to the exponent of a single prime, and
then recognizing the resulting coefficient identities as a formal-power-series
differential equation.

*References:*
- [A317940](https://oeis.org/A317940)
- [A046644](https://oeis.org/A046644)
- [A005187](https://oeis.org/A005187)
-/

namespace OeisA317940

open Nat Finset

/--
A005187: the sum of $\lfloor e / 2^k \rfloor$ over $k \ge 0$.
-/
noncomputable def a005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2 ^ k)

/--
A046644: the multiplicative function whose value at each prime power $p^e$ is
$2^{\operatorname{A005187}(e)}$.
-/
noncomputable def a046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (a005187 e)

/--
The rational sequence whose Dirichlet convolution square is A046644, written
using the defining recurrence from the OEIS entry.
-/
noncomputable def f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let target : ℚ := a046644 n
      let interiorSum : ℚ := Finset.sum (divisors n) fun d ↦
        if h : d > 1 ∧ d < n then
          have d_lt_n : d < n := h.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h.1
          IH d d_lt_n * IH q q_lt_n
        else 0
      (target - interiorSum) / 2

/--
A317940: the numerator of `f n`.
-/
noncomputable def a (n : ℕ) : ℤ :=
  (f n).num

/-- The defining recurrence of `f`, with the recursive calls folded back to `f`. -/
@[category API, AMS 11]
private lemma f_eq (n : ℕ) :
    f n = if n = 0 then 0 else if n = 1 then 1 else
      (a046644 n -
        ∑ d ∈ n.divisors, if _h : 1 < d ∧ d < n then f d * f (n / d) else 0) / 2 := by
  conv_lhs => rw [f, WellFounded.fix_eq]
  rfl

@[category API, AMS 11]
private lemma f_one : f 1 = 1 := by
  rw [f_eq]; norm_num

/-- At a prime `p` every divisor is `1` or `p`, so the interior sum is empty. -/
@[category API, AMS 11]
private lemma f_prime {p : ℕ} (hp : p.Prime) : f p = a046644 p / 2 := by
  rw [f_eq, if_neg hp.ne_zero, if_neg hp.ne_one,
    Finset.sum_eq_zero (fun x hx => ?_)]
  · ring
  · rcases hp.eq_one_or_self_of_dvd x (Nat.mem_divisors.mp hx).1 with rfl | rfl
    · exact dif_neg (by omega)
    · exact dif_neg (by omega)

@[category API, AMS 11]
private lemma f_two : f 2 = 1 := by
  rw [f_prime Nat.prime_two]; norm_num [a046644, a005187]

@[category API, AMS 11]
private lemma f_three : f 3 = 1 := by
  rw [f_prime Nat.prime_three]; norm_num [a046644, a005187]

@[category API, AMS 11]
private lemma f_five : f 5 = 1 := by
  rw [f_prime (by norm_num)]; norm_num [a046644, a005187]

/-- `4 = 2 ^ 2` is the only case here with a nonempty interior sum, contributing `f 2 * f 2`. -/
@[category API, AMS 11]
private lemma f_four : f 4 = 7 / 2 := by
  rw [f_eq 4]
  norm_num only
  rw [show (Nat.divisors 4) = {1, 2, 4} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    dif_neg (by omega), dif_pos (by omega), dif_neg (by omega),
    show a046644 4 = 8 from ?_]
  · rw [f_two]; norm_num
  · rw [a046644, if_neg (by norm_num), show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_two]
    norm_num [Finsupp.prod_single_index, a005187, Finset.sum_range_succ]

/-- `f 1 = 1` is the base case of the recurrence, so `a 1 = 1`. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [a, f_one]
  rfl

/-- `2` is prime, so the interior sum is empty and `f 2 = a046644 2 / 2 = 1`. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rw [a, f_two]
  rfl

/-- `3` is prime, so the interior sum is empty and `f 3 = a046644 3 / 2 = 1`. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  rw [a, f_three]
  rfl

/-- `4` is the first index with a nonempty interior sum, giving `f 4 = 7 / 2`. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by
  rw [a, f_four]
  norm_num

/-- `5` is prime, so the interior sum is empty and `f 5 = a046644 5 / 2 = 1`. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  rw [a, f_five]
  rfl

/--
"No negative terms among the first 2^20 terms. Is the sequence nonnegative?"

Equivalently, the rational Dirichlet square root `f` is nonnegative at every
positive index. Informally, the proof constructs a strictly positive
multiplicative square root prime-power by prime-power using formal power
series, and then identifies it with the recursively defined sequence `f`.

The proof was obtained by exploiting the multiplicativity of A046644 and
reducing the problem to its values on prime powers. The resulting convolution
recurrence for the prime-power coefficients was recognized as a
formal-power-series identity. A positive coefficient sequence was constructed
through a differential equation for the generating series, extended
multiplicatively to all positive integers, and finally identified with the
recursively defined Dirichlet square root by uniqueness.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean"]
theorem f_nonnegative (n : ℕ) (h : n > 0) : f n ≥ 0 := by
  sorry

end OeisA317940