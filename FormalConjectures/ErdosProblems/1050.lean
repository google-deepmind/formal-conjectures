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
# Erdős Problem 1050

*Reference:* [erdosproblems.com/1050](https://www.erdosproblems.com/1050)

Is $\sum_{n=1}^{\infty} \frac{1}{2^n - 3}$ irrational?

Erdős [Er48] proved that $\sum 1/(2^n - 1) = \sum \tau(n)/2^n$ is irrational (where
$\tau(n)$ is the divisor function). He notes [Er88c] that $\sum 1/(2^n + t)$ should be
transcendental for every integer $t$ (with the obvious exception $t = 0$).

This was proved by Borwein [Bo91], who more generally proved that, for any
integer $q \geq 2$ and rational $r \neq 0$ (distinct from $-q^n$ for all $n \geq 1$), the
series $\sum_{n=1}^{\infty} 1/(q^n + r)$ is irrational.

[Er48] Erdős, P., _On arithmetical properties of Lambert series_. J. Indian Math. Soc. (N.S.)
(1948), 63-66.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[Er88c] Erdős, P., _On the irrationality of certain series: problems and results_. New advances
in transcendence theory (Durham, 1986) (1988), 102-109.

[Bo91] Borwein, P., _On the irrationality of $\sum(1/(q^n+r))$_. J. Number Theory (1991),
253-259.
-/

namespace Erdos1050

/--
Erdős Problem 1050 [ErGr80, p.62] [Er88c, p.102]:

The sum $\sum_{n=1}^{\infty} \frac{1}{2^n - 3}$ is irrational.

Proved by Borwein [Bo91].
-/
@[category research solved, AMS 11 40]
theorem erdos_1050 : answer(True) ↔
    Irrational (∑' (n : ℕ+), (1 : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 3)) := by
  sorry

/--
Borwein's general irrationality result [Bo91]: for any integer $q \geq 2$ and rational
$r \neq 0$ (with $r \neq -q^n$ for all $n \geq 1$), the series
$\sum_{n=1}^{\infty} 1/(q^n + r)$ is irrational.
-/
@[category research solved, AMS 11 40]
theorem erdos_1050.variants.borwein_general (q : ℤ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hqr : ∀ n : ℕ+, (r : ℝ) ≠ -(q : ℝ) ^ (n : ℕ)) :
    Irrational (∑' n : ℕ+, 1 / ((q : ℝ) ^ (n : ℕ) + (r : ℝ))) := by
  sorry

/--
Erdős conjectured [Er88c] that $\sum 1/(2^n + t)$ should be transcendental for every
nonzero integer $t$ (with $t \neq -2^n$ for all $n \geq 1$). Borwein [Bo91] proved
irrationality but the transcendence question remains open.
-/
@[category research open, AMS 11 40]
theorem erdos_1050.variants.transcendence :
    answer(sorry) ↔ ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ+, (t : ℝ) ≠ -(2 : ℝ) ^ (n : ℕ)) →
      Transcendental ℚ (∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) + (t : ℝ))) := by
  sorry

end Erdos1050
