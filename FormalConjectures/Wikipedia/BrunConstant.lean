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
# Irrationality of Brun's twin prime constant

Applying his combinatorial sieve in 1919, Viggo Brun established that the reciprocal sum over twin
prime pairs
$$B_2 = \sum_{p, p + 2 \text{ prime}} \left(\frac{1}{p} + \frac{1}{p + 2}\right)
  = \left(\frac{1}{3} + \frac{1}{5}\right) + \left(\frac{1}{5} + \frac{1}{7}\right) +
    \left(\frac{1}{11} + \frac{1}{13}\right) + \cdots \approx 1.9021605831$$
(OEIS A065421, counting $1 / 5$ in both $(3, 5)$ and $(5, 7)$) is finite, unlike Euler's divergent
series over all primes. Since finitely many rational terms always have a rational sum,
irrationality of $B_2$ would entail infinitely many twin primes; whether $B_2$ is irrational
remains open.

*References:*
- [Wikipedia: Brun's theorem](https://en.wikipedia.org/wiki/Brun%27s_theorem)
- [OEIS A065421](https://oeis.org/A065421)
- V. Brun, *La série $\frac{1}{5} + \frac{1}{7} + \frac{1}{11} + \frac{1}{13} + \frac{1}{17} +
  \frac{1}{19} + \frac{1}{29} + \frac{1}{31} + \frac{1}{41} + \frac{1}{43} + \frac{1}{59} +
  \frac{1}{61} + \cdots$ où les dénominateurs sont «nombres premiers jumeaux» est convergente ou
  finie*, Bull. Sci. Math. (2) **43** (1919), 100–104, 124–128.
- S. R. Finch, *Mathematical Constants*, Cambridge Univ. Press (2003), §2.13, 133–135.
-/

@[expose] public section

namespace BrunConstant

/-- $p = 3$ begins the twin prime pair $(3, 5)$. -/
@[category test, AMS 11]
theorem isTwinPrimeLower_three : IsTwinPrimeLower 3 := by
  unfold IsTwinPrimeLower
  norm_num

/-- The twin prime pair starting at $p = 3$ has reciprocal sum $1/3 + 1/5 = 8/15$. -/
@[category test, AMS 11]
theorem twinPrimeTerm_three : twinPrimeTerm 3 = 8 / 15 := by
  unfold twinPrimeTerm
  norm_num

/-- $p = 7$ is not the lesser member of a twin prime pair because $9$ is composite. -/
@[category test, AMS 11]
theorem not_isTwinPrimeLower_seven : ¬ IsTwinPrimeLower 7 := by
  unfold IsTwinPrimeLower
  norm_num

/-- Irrationality of $B_2$ implies infinitely many twin primes, as finitely many twin prime pairs
would make $B_2$ rational. -/
@[category API, AMS 11]
theorem irrational_brunConstant_imp_infinite_twin_primes (hirr : Irrational brunConstant) :
    {p : ℕ | IsTwinPrimeLower p}.Infinite := by
  intro hfin
  let _ : Fintype {p : ℕ // IsTwinPrimeLower p} := hfin.fintype
  let q : ℚ := ∑ p : {p : ℕ // IsTwinPrimeLower p},
    ((1 : ℚ) / (p.1 : ℚ) + (1 : ℚ) / ((p.1 : ℚ) + 2))
  have hrat : brunConstant = (q : ℝ) := by
    unfold brunConstant twinPrimeTerm q
    rw [tsum_fintype]
    push_cast
    rfl
  exact hirr.ne_rat q hrat

/--
**Brun's Theorem** (1919): the twin prime reciprocal series
$\sum_{p, p+2 \text{ prime}} (1/p + 1/(p + 2))$ is summable in $\mathbb{R}$.
-/
@[category textbook, AMS 11]
theorem brun_twin_prime_summable :
    Summable (fun p : {p : ℕ // IsTwinPrimeLower p} => twinPrimeTerm p.1) := by
  sorry

/--
Is Brun's twin prime constant $B_2$ irrational?
-/
@[category research open, question, AMS 11]
theorem brun_constant_irrational : Irrational brunConstant := by
  sorry

end BrunConstant
