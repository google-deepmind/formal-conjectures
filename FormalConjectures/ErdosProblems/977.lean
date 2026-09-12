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
# Erdős Problem 977

*References:*
- [erdosproblems.com/977](https://www.erdosproblems.com/977)
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [La21] L. Lai, *On the largest prime divisor of $n!+1$*. arXiv:2103.14894 (2021).
- [MuWo02] Murty, Ram and Wong, Siman, *The {$ABC$} conjecture and prime divisors of the {L}ucas and
  {L}ehmer sequences*. (2002), 43--54.
- [Sc62] Schinzel, A., *On primitive prime factors of {$a^n-b^n$}*. Proc. Cambridge Philos. Soc.
  (1962), 555--562.
- [St13] Stewart, Cameron L., *On divisors of {L}ucas and {L}ehmer numbers*. Acta Math. (2013),
  291--314.
- [St74b] Stewart, C. L., *The greatest prime factor of {$a^n-b^n$}*. Acta Arith. (1974/75),
  427--433.
-/

open Filter Real
open scoped Asymptotics

namespace Erdos977

/--
If $P(m)$ is the greatest prime divisor of $m$, then is it true that
$$\frac{P(2^n-1)}{n}\to \infty$$
as $n\to \infty$?

This was proved in the affirmative by Stewart [St13], who proved that
$$P(2^n-1)\gg n^{1+\frac{1}{104\log\log n}}$$
for all large $n$.
-/
@[category research solved, AMS 11]
theorem erdos_977 : answer(True) ↔
    Tendsto (fun n : ℕ ↦ ((2 ^ n - 1).maxPrimeFac : ℝ) / n) atTop atTop := by
  sorry

/--
Schinzel [Sc62] proved that $P(2^n-1)>2n$ for $n>12$.
-/
@[category research solved, AMS 11]
theorem erdos_977.variants.schinzel :
    ∀ n > 12, 2 * n < (2 ^ n - 1).maxPrimeFac := by
  sorry

/--
Stewart [St74b] proved that this conjecture is true if we restrict $n$ to those integers with
$<\frac{1}{\log 2}\log\log n$ many prime factors.
-/
@[category research solved, AMS 11]
theorem erdos_977.variants.stewart_few_prime_factors :
    Tendsto (fun n : ℕ ↦ ((2 ^ n - 1).maxPrimeFac : ℝ) / n)
      (atTop ⊓ principal {n : ℕ | (n.primeFactors.card : ℝ) < log (log n) / log 2}) atTop := by
  sorry

/--
This was proved in the affirmative by Stewart [St13], who proved that
$$P(2^n-1)\gg n^{1+\frac{1}{104\log\log n}}$$
for all large $n$.
-/
@[category research solved, AMS 11]
theorem erdos_977.variants.stewart :
    (fun n : ℕ ↦ (n : ℝ) ^ (1 + 1 / (104 * log (log n)))) =O[atTop]
      fun n ↦ ((2 ^ n - 1).maxPrimeFac : ℝ) := by
  sorry

/--
In [Er65b] Erdős also asks about $P(n!+1)$. The case of $P(n!+1)$ appears to be open still.
-/
@[category research open, AMS 11]
theorem erdos_977.variants.factorial : answer(sorry) ↔
    Tendsto (fun n : ℕ ↦ ((n.factorial + 1).maxPrimeFac : ℝ) / n) atTop atTop := by
  sorry

/--
Murty and Wong [MuWo02] proved that
$$P(n!+1)>(1+o(1))n\log n$$
assuming the abc conjecture.
-/
@[category research solved, AMS 11]
theorem erdos_977.variants.murty_wong :
    (∀ ε > (0 : ℝ),
      {(a, b, c) : ℕ × ℕ × ℕ |
        0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
          (((a * b * c).primeFactors.prod (id : ℕ → ℕ) : ℕ) : ℝ) ^ (1 + ε) < c}.Finite) →
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 - ε) * n * log n < ((n.factorial + 1).maxPrimeFac : ℝ) := by
  sorry

/--
The best-known unconditional result, due to Lai [La21], is that
$$\limsup \frac{P(n!+1)}{n} \geq 1+9\log 2\approx 7.238.$$
-/
@[category research solved, AMS 11]
theorem erdos_977.variants.lai :
    (1 + 9 * log 2 : EReal) ≤
      atTop.limsup (fun n : ℕ ↦ (((n.factorial + 1).maxPrimeFac : ℝ) / n : EReal)) := by
  sorry

end Erdos977
