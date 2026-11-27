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
module

public import FormalConjecturesUtil

/-!
# The sequence with $1 = \sum_{n \ge 0} a(n) x^n / (1 + 3^n x)^{n+1}$

The sequence is defined by $1 = \sum_{n \ge 0} a(n) x^n / (1 + 3^n x)^{n+1}$. Comparing the
coefficients of $x^n$ gives $a(0) = 1$ and, for $n \ge 1$,
$$a(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} 3^{k(n-k)} a(n-k).$$
$a(n)$ is also the number of acyclic 2-multidigraphs. With $2^n$ in place of $3^n$, the same
identity defines [A003024](https://oeis.org/A003024), the number of labeled acyclic digraphs.

*References:*
- [A188457](https://oeis.org/A188457), Paul D. Hanna, 2011.
-/

@[expose] public section

namespace OeisA188457

open PowerSeries

/-- The sequence $a_q$ for an integer $q$: $a_q(0) = 1$ and
$a_q(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} q^{k(n-k)} a_q(n-k)$ for $n \ge 1$. The case
$q = 3$ is A188457. The sum runs over `(Finset.Icc 1 n).attach` so that Lean can check
termination. -/
def a (q : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    ∑ k ∈ (Finset.Icc 1 n).attach,
      (-1) ^ (k.1 + 1) * (n.choose k.1 : ℤ) * q ^ (k.1 * (n - k.1)) * a q (n - k.1)
decreasing_by have := Finset.mem_Icc.mp k.2; omega

@[category test, AMS 11]
theorem a_0 : a 3 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 3 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 3 2 = 5 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 3 = 109 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 3 4 = 9449 := by
  sorry

/-- The series $\sum_{n \ge 1} a_q(n) x^n / n$ over $\mathbb{Q}$. Its exponential is
`subst (logSeries q) (exp ℚ)`. -/
noncomputable def logSeries (q : ℤ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (a q n : ℚ) / n

/--
"exp( Sum_{n >= 1} a(n)*x^n/n ) = 1 + x + 3*x^2 + 39*x^3 + 2403*x^4 + 616131*x^5 + ... appears
to have integer coefficients."
- Peter Bala, Jan 14 2016.

Proved by Wentao Li, with AI assistance, as the case $q = 3$ of `OeisA3024.exp_integral`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem conjecture (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (logSeries 3) (exp ℚ)) = z := by
  sorry

end OeisA188457

end
