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
# Erdős Problem 700

*Reference:* [erdosproblems.com/700](https://www.erdosproblems.com/700)

A problem of Erdős and Szekeres on the function
$f(n) = \min_{1 < k \le n/2} \gcd(n, \binom{n}{k})$ for composite $n$.

It is easy to see that $f(n) \le n/P(n)$ for composite $n$, and that $f(n) \ge p(n)$
(the smallest prime factor). Hence $f(n) \ge n^{1/2}$ when $n = p^2$, and
$f(n) \le (1+o(1))\, n / \log n$ in general. It is known that $f(n) = n/P(n)$ when $n$
is a product of two primes, or $n = 30$.

[ErSz78] Erdős, P. and Szekeres, G., 1978.
-/

namespace Erdos700

/-- $f(n) = \min_{1 < k \le n/2} \gcd(n, \binom{n}{k})$ for $n \ge 4$;
defined as $0$ for $n < 4$. -/
def f (n : ℕ) : ℕ :=
  if h : 4 ≤ n then
    ((Finset.Icc 2 (n / 2)).image (fun k => Nat.gcd n (Nat.choose n k))).min' (by
      exact ⟨Nat.gcd n (Nat.choose n 2), Finset.mem_image.mpr
        ⟨2, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩, rfl⟩⟩)
  else 0

/-- The largest prime factor of $n$. Returns $0$ if $n \le 1$. -/
def greatestPrimeFactor (n : ℕ) : ℕ := n.primeFactorsList.foldl max 0

/--
Erdős Problem 700, Part (a) [ErSz78]:
For any composite $n \ge 4$, $f(n) \le n / P(n)$ where $P(n)$ is the largest prime factor.
The characterization of those $n$ where equality holds is the open question.
-/
@[category research solved, AMS 11]
theorem erdos_700.variants.upper_bound (n : ℕ) (hn : 4 ≤ n) (hcomp : ¬ Nat.Prime n) :
    f n ≤ n / greatestPrimeFactor n := by
  sorry

/--
Erdős Problem 700, Part (b) [ErSz78]:
Are there infinitely many composite $n$ such that $f(n) > \sqrt{n}$?
Here $f(n) > \sqrt{n}$ is stated as $f(n)^2 > n$ to remain in $\mathbb{N}$.
-/
@[category research open, AMS 11]
theorem erdos_700.variants.infinitely_many_large :
    answer(sorry) ↔
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ Nat.Prime n ∧ 2 ≤ n ∧ (f n) ^ 2 > n := by
  sorry

/--
Erdős Problem 700, Part (c) [ErSz78]:
Is it true that, for every composite $n$, $f(n) \ll_A n / (\log n)^A$ for every $A > 0$?

Formalized as: for every positive integer $A$, there exist $C > 0$ and $N_0$ such that
for all composite $n \ge N_0$, $f(n) \le C \cdot n / (\log n)^A$.
-/
@[category research open, AMS 11]
theorem erdos_700 :
    answer(sorry) ↔
    ∀ A : ℕ, 0 < A →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ Nat.Prime n → 2 ≤ n →
      (f n : ℝ) ≤ C * (n : ℝ) / (Real.log (n : ℝ)) ^ A := by
  sorry

end Erdos700
