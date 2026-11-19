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
# OEIS A003024 and A188457, Bala's integrality conjectures

For an integer $q$ define $a_q(0) = 1$ and, for $n \ge 1$,
$$a_q(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} q^{k(n-k)} a_q(n-k). \tag{R}$$
Lean's convention $0^0 = 1$ is used at $q = 0$.

- $a_2$ is OEIS A003024, the number of labeled acyclic digraphs on $n$ nodes. (R) with $q = 2$
  is the recurrence in its formula section (Robinson 1973, Stanley 1973).
- $a_3$ is OEIS A188457, the number of acyclic 2-multidigraphs. Its name defines it by
  $1 = \sum_{n \ge 0} a(n) x^n / (1 + 3^n x)^{n+1}$. Taking the coefficient of $x^N$ gives
  $\sum_{k=0}^{N} (-1)^k \binom{N}{k} 3^{k(N-k)} a(N-k) = [N = 0]$, which is (R) with $q = 3$.
- OEIS A188490 (Paul D. Hanna, 2011) is defined by its g.f.
  $\exp\left(\sum_{n \ge 1} \mathrm{A003024}(n) x^n / n\right)$.

Peter Bala (2016) notes in A003024 and in A188457 that
$\exp\left(\sum_{n \ge 1} a(n) x^n / n\right)$ appears to have integer coefficients. The file
states this for every integer $q$, together with the Gauss congruences that imply it.

Integer coefficients are stated as `∀ n, ∃ z : ℤ, coeff n F = z`, and $\exp$ of a series $L$
with zero constant term as `subst L (exp ℚ)`.

*References:*
- [A003024](https://oeis.org/A003024), [A188457](https://oeis.org/A188457) and
  [A188490](https://oeis.org/A188490).
- R. W. Robinson, *Counting labeled acyclic digraphs*, in New Directions in the Theory of
  Graphs, Academic Press, 1973, 239–273.
- R. P. Stanley, *Acyclic orientations of graphs*, Discrete Math. 5 (1973), 171–178.
-/

@[expose] public section

namespace OeisA3024

open PowerSeries

/-- The sequence $a_q$, defined by $a_q(0) = 1$ and the recurrence (R)
$a_q(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} q^{k(n-k)} a_q(n-k)$ for $n \ge 1$.
The sum runs over `(Finset.Icc 1 n).attach` so that the recursive call is visibly on a
smaller argument. -/
def a (q : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    ∑ k ∈ (Finset.Icc 1 n).attach,
      (-1) ^ (k.1 + 1) * (n.choose k.1 : ℤ) * q ^ (k.1 * (n - k.1)) * a q (n - k.1)
decreasing_by have := Finset.mem_Icc.mp k.2; omega

/-- The series $\sum_{n \ge 1} a_q(n) x^n / n$ over $\mathbb{Q}$. -/
noncomputable def logSeries (q : ℤ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (a q n : ℚ) / n

/-- **Gauss congruences.** For every integer $q$, every prime $p$ and all $n, r \ge 1$,
$a_q(n p^r) \equiv a_q(n p^{r-1}) \pmod{p^r}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem gauss_congruence (q : ℤ) {p : ℕ} (hp : p.Prime) {n r : ℕ} (_hn : 0 < n) (hr : 0 < r) :
    a q (n * p ^ r) ≡ a q (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ r] := by
  sorry

/-- **Integrality for every $q$.** For every integer $q$,
$\exp\left(\sum_{n \ge 1} a_q(n) x^n / n\right)$ has integer coefficients. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem exp_integral (q : ℤ) (n : ℕ) : ∃ z : ℤ, coeff n (subst (logSeries q) (exp ℚ)) = z := by
  sorry

/-- **Bala's conjecture in A003024** ($q = 2$): the series
$\exp\left(\sum_{n \ge 1} \mathrm{A003024}(n) x^n / n\right) = 1 + x + 2x^2 + 10x^3 + \dots$
has integer coefficients. Its coefficients are the terms of A188490, so every term of A188490
is an integer. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem a003024_exp_integral (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (logSeries 2) (exp ℚ)) = z := by
  sorry

/-- **Bala's conjecture in A188457** ($q = 3$): the series
$\exp\left(\sum_{n \ge 1} \mathrm{A188457}(n) x^n / n\right) = 1 + x + 3x^2 + 39x^3 + \dots$
has integer coefficients. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000016"]
theorem a188457_exp_integral (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (logSeries 3) (exp ℚ)) = z := by
  sorry

end OeisA3024

end
