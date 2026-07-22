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
# Conjectures associated with A363102

Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$

A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.

*References:*
- [A363102](https://oeis.org/A363102)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [A051403](https://oeis.org/A051403)
-/

namespace OeisA363102


open Nat Finset

/--
Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$
-/
def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

/--
A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  -- The subtraction n^2 - 2 is safe for n >= 3.
  num / Nat.gcd num denom_arg


@[category test, AMS 11]
lemma a_three : a 3 = 7 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 7 := by rfl

@[category test, AMS 11]
lemma a_five : a 5 = 23 := by rfl

@[category test, AMS 11]
lemma a_six : a 6 = 17 := by rfl

@[category test, AMS 11]
lemma a_seven : a 7 = 47 := by rfl


/--
Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$

A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/363102.wip.lean#L283"]
theorem a_eq_one_or_prime : ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := by
    sorry

end OeisA363102
