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
# Number of acyclic digraphs with $n$ labeled nodes

The sequence counts the acyclic digraphs (DAGs) with $n$ labeled nodes. It satisfies $a(0) = 1$
and, for $n \ge 1$, the recurrence
$$a(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} 2^{k(n-k)} a(n-k)$$
of Robinson and Stanley.

*References:*
- [A003024](https://oeis.org/A003024), N. J. A. Sloane.
- R. W. Robinson, *Counting labeled acyclic digraphs*, in New Directions in the Theory of
  Graphs, Academic Press, 1973, 239–273.
- R. P. Stanley, *Acyclic orientations of graphs*, Discrete Math. 5 (1973), 171–178.
-/

@[expose] public section

namespace OeisA3024

open PowerSeries

/-- The sequence $a_q$ for an integer $q$: $a_q(0) = 1$ and
$a_q(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} q^{k(n-k)} a_q(n-k)$ for $n \ge 1$. The case
$q = 2$ is A003024. At $q = 0$, Lean's convention $0^0 = 1$ applies. The sum runs over
`(Finset.Icc 1 n).attach` so that Lean can check termination. -/
def a (q : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    ∑ k ∈ (Finset.Icc 1 n).attach,
      (-1) ^ (k.1 + 1) * (n.choose k.1 : ℤ) * q ^ (k.1 * (n - k.1)) * a q (n - k.1)
decreasing_by have := Finset.mem_Icc.mp k.2; omega

@[category test, AMS 11]
theorem a_0 : a 2 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 2 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 2 = 3 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 2 3 = 25 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 2 4 = 543 := by
  sorry

/-- The series $\sum_{n \ge 1} a_q(n) x^n / n$ over $\mathbb{Q}$. Its exponential is
`subst (logSeries q) (exp ℚ)`. -/
noncomputable def logSeries (q : ℤ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (a q n : ℚ) / n

/-- For every integer $q$, every prime $p$ and all $n, r \ge 1$,
$a_q(n p^r) \equiv a_q(n p^{r-1}) \pmod{p^r}$.

Proved by Wentao Li, with AI assistance. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem gauss_congruence (q : ℤ) {p : ℕ} (hp : p.Prime) {n r : ℕ} (_hn : 0 < n) (hr : 0 < r) :
    a q (n * p ^ r) ≡ a q (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ r] := by
  sorry

/-- For every integer $q$, the series $\exp\left(\sum_{n \ge 1} a_q(n) x^n / n\right)$ has
integer coefficients.

Proved by Wentao Li, with AI assistance, from `gauss_congruence` and Dold's integrality
criterion. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem exp_integral (q : ℤ) (n : ℕ) : ∃ z : ℤ, coeff n (subst (logSeries q) (exp ℚ)) = z := by
  sorry

/--
"exp( Sum_{n >= 1} a(n)*x^n/n ) = 1 + x + 2*x^2 + 10*x^3 + 146*x^4 + 6010*x^5 + ... appears to
have integer coefficients (cf. A188490)."
- Peter Bala, Jan 14 2016.

Proved by Wentao Li, with AI assistance, as the case $q = 2$ of `exp_integral`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem conjecture (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (logSeries 2) (exp ℚ)) = z := by
  sorry

end OeisA3024

end
