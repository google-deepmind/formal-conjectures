/-
Copyright 2025 The Formal Conjectures Authors.

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
# Open questions on irrationality of numbers

*References:*
- [Wikipedia, Irrational number](https://en.wikipedia.org/wiki/Irrational_number#Open_questions)
- [Wikipedia, Euler-Lehmer constants](https://en.wikipedia.org/wiki/Euler%27s_constant#Euler-Lehmer_constants)
- [Wikipedia, Transcendental number](https://en.wikipedia.org/wiki/Transcendental_number)
-/

open Real Finset Filter

local notation "e" => exp 1

/--
**Generalized Euler-Lehmer sequence**
* `a` - residue class modulo `q`
* `n` - upper bound for summation

The sequence calculates the difference between:
1. The sum of reciprocals of natural numbers ≤ `n` congruent to `a` modulo `q`
2. The natural logarithm of `n` scaled by `1/q`

`eulerMascheroniSeq` occurs when `q=1` and `a=1`.
-/
noncomputable def eulerLehmerSeq (a : ℕ) (q : ℕ+) (n : ℕ) : ℝ :=
  let S (x : ℕ) := ∑ k in (Finset.Icc 1 x).filter (· ≡ a [MOD (q : ℕ)]), (1 : ℝ) / k
  S n - log n / q

/--
**Euler-Lehmer constant** for residue class `a` modulo `q`.
*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Euler%27s_constant#Euler-Lehmer_constants)
-/
noncomputable def eulerLehmerConstant (a : ℕ) (q : ℕ+) : ℝ :=
  limUnder atTop (eulerLehmerSeq a q)

/--
**Catalan's constant**
$$G = ∑_{n=0}^∞ (-1)^n / (2n + 1)^2 \approx 0.91596$$
-/
noncomputable def catalanConstant : ℝ :=
  ∑' n : ℕ, (-1)^n / (2*n + 1)^2

/--
**Gompertz constant**
$$\delta = -e * ∫_1^∞ e^{-t}/t dt \approx 0.59634$$
-/
noncomputable def gompertzConstant : ℝ :=
  -e * ∫ (t:ℝ) in Set.Ioi 1, exp (-t) / t

/--
$e + \pi$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_e_plus_pi : Irrational (e + π) := by
  sorry

/--
$e \pi$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_e_times_pi : Irrational (e * π) := by
  sorry

/--
$e ^ e$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_e_to_e : Irrational (e ^ e) := by
  sorry

/--
$\pi ^ e$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_pi_to_e : Irrational (π ^ e) := by
  sorry

/--
$\pi ^ \pi$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_pi_to_pi : Irrational (π ^ π) := by
  sorry

/--
$\ln(\pi)$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_ln_pi : Irrational (log π) := by
  sorry

/--
Euler-Mascheroni constant $\gamma$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_euler_mascheroni_constant : Irrational eulerMascheroniConstant := by
  sorry

/--
At least one of Catalan constant and the Gompertz constant is irrational.
-/
@[category research solved, AMS 11 33]
theorem irrational_catalan_or_gompertz : Irrational catalanConstant ∨ Irrational gompertzConstant := by
  sorry

/--
The Catalan constant $G$ is irrational.
-/
@[category research open, AMS 11, AMS 33]
theorem irrational_catalan_constant : Irrational catalanConstant := by
  sorry

/--
The Gompertz constant $\delta$ is irrational.
-/
@[category research open, AMS 33]
theorem irrational_gompertz_constant : Irrational gompertzConstant := by
  sorry

/--
$\Gamma(1/2)$ is irrational.

[Ch84] Chudnovsky, G. (1984). Contributions to the theory of transcendental numbers.
-/
@[category research solved, AMS 33]
theorem irrational_gamma_1_2 : Irrational (1/2 : ℝ).Gamma := by
  sorry

/--
$\Gamma(1/3)$ is irrational.

[Ch84] Chudnovsky, G. (1984). Contributions to the theory of transcendental numbers.
-/
@[category research solved, AMS 33]
theorem irrational_gamma_1_3 : Irrational (1/3 : ℝ).Gamma := by
  sorry

/--
$\Gamma(1/4)$ is irrational.

[Ch84] Chudnovsky, G. (1984). Contributions to the theory of transcendental numbers.
-/
@[category research solved, AMS 33]
theorem irrational_gamma_1_4 : Irrational (1/4 : ℝ).Gamma := by
  sorry

/--
$\Gamma(1/6)$ is irrational.

[Ch84] Chudnovsky, G. (1984). Contributions to the theory of transcendental numbers.
-/
@[category research solved, AMS 33]
theorem irrational_gamma_1_6 : Irrational (1/6 : ℝ).Gamma := by
  sorry

/--
$\Gamma(1/n)$ for `n ≥ 2` is irrational.
-/
@[category research open, AMS 33]
theorem irrational_gamma_1_n (n : ℕ) (hn : 1 < n) : Irrational (1/4 : ℝ).Gamma := by
  sorry

/--
$\Gamma(1/n)$ for `n ≥ 2` is irrational.
-/
@[category research open, AMS 33]
theorem exists_irrational_euler_lehmer_constant (n : ℕ) (hn : 1 < n) :
  (∃ (q : ℕ+), ∃ (a : ℕ) (ha : a < q), Irrational (eulerLehmerConstant a q)) ↔ answer(sorry) := by
  sorry
