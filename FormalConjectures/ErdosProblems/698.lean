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
# Erdős Problem 698

*References:*
- [erdosproblems.com/698](https://www.erdosproblems.com/698)
- [ErSz78] Erdős, P. and Szekeres, G., *Some number theoretic problems on binomial
  coefficients*. Austral. Math. Soc. Gaz. (1978), 97-99.
- [Be11] Bergman, George M., *On common divisors of multinomial coefficients*. Bull. Aust.
  Math. Soc. (2011), 138--157.
-/

namespace Erdos698

open Filter

/--
Is there some $h(n)\to \infty$ such that for all $2\leq i<j\leq n/2$
\[\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq h(n)?\]

This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$
\[\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},\]
where the implied constant is absolute.
-/
@[category research solved, AMS 5 11]
theorem erdos_698 : answer(True) ↔
    ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
      ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
        h n ≤ Nat.gcd (n.choose i) (n.choose j) := by
  sorry

/--
A problem of Erdős and Szekeres, who observed that
\[\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq \frac{\binom{n}{i}}{\binom{j}{i}}
\geq 2^i\]
(in particular the greatest common divisor is always $>1$).
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.erdos_szekeres (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n / 2) :
    (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) := by
  sorry

/--
This inequality is sharp for $i=1$, $j=p$, and $n=2p$.
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.erdos_szekeres_sharp (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
        ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
      ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1 := by
  sorry

/--
This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$
\[\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},\]
where the implied constant is absolute.
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.bergman :
    ∃ c : ℝ, 0 < c ∧ ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
      c * (Real.sqrt (n : ℝ) * (2 : ℝ) ^ i / ((i : ℝ) * Real.sqrt (i : ℝ))) ≤
        (Nat.gcd (n.choose i) (n.choose j) : ℝ) := by
  sorry

end Erdos698
