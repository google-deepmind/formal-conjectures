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
# Conjectures associated with a

Helper function for a, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.

*References:*
- [A363347](https://oeis.org/A363347)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA363347


open Rat Nat

/--
Helper function for a, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
a: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$.
If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


@[category test, AMS 11]
lemma a_three : a 3 = 11 := by delta a; repeat rw [continued_fraction_denominator]; norm_num

@[category test, AMS 11]
lemma a_four : a 4 = 5 := by delta a; repeat rw [continued_fraction_denominator]; norm_num

@[category test, AMS 11]
lemma a_five : a 5 = 31 := by delta a; repeat rw [continued_fraction_denominator]; norm_num

@[category test, AMS 11]
lemma a_six : a 6 = 11 := by delta a; repeat rw [continued_fraction_denominator]; norm_num

@[category test, AMS 11]
lemma a_seven : a 7 = 59 := by delta a; repeat rw [continued_fraction_denominator]; norm_num


/--
Helper function for a, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/363347.wip.lean#L825"]
theorem target_theorem_0
  : ∀ p : ℕ, (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) → ∃ n : ℕ, a n = p := by
    sorry

end OeisA363347
