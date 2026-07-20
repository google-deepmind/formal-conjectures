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

@[category test, AMS 11]
theorem test_a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem test_a_2 : a 2 = 1 := by
  sorry

@[category test, AMS 11]
theorem test_a_3 : a 3 = 1 := by
  sorry

@[category test, AMS 11]
theorem test_a_4 : a 4 = 7 := by
  sorry

@[category test, AMS 11]
theorem test_a_5 : a 5 = 1 := by
  sorry

/--
"No negative terms among the first 2^20 terms. Is the sequence nonnegative?"

Equivalently, the rational Dirichlet square root `f` is nonnegative at every
positive index. Informally, the proof constructs a strictly positive
multiplicative square root prime-power by prime-power using formal power
series, and then identifies it with the recursively defined sequence `f`.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean"]
theorem f_nonnegative (n : ℕ) (h : n > 0) : f n ≥ 0 := by
  sorry

end OeisA317940
