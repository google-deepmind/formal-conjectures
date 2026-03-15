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
# Erdős Problem 227

Let $f = \sum a_n z^n$ be an entire function which is not a polynomial. Is it true that if
the limit of the ratio of the maximum term to the maximum modulus exists, then it must be $0$?
This was disproved by Clunie and Hayman [ClHa64], who showed the limit can take any value
in $[0, 1/2]$. Clunie (unpublished) proved the statement does hold when all coefficients
$a_n \geq 0$.

See also Problem 513.

*Reference:* [erdosproblems.com/227](https://www.erdosproblems.com/227)

[Er57] Erdős, P., _Some unsolved problems_, 1957.
[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató
Int. Közl. **6** (1961), 221–254.
[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_,
L'Enseignement Math. **27** (1982), 163–176.
[ClHa64] Clunie, J. and Hayman, W. K., _The maximum term of a power series_.
J. Analyse Math. (1964), 143–186.
-/

open Complex Filter

open scoped Topology

namespace Erdos227

/--
The maximum term of a power series with coefficients $a$ at radius $r$:
$\mu(r) = \sup_n \|a_n\| \cdot r^n$
-/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖a n‖ * r ^ n

/--
The maximum modulus of $f$ on the circle of radius $r$:
$M(r) = \sup\{\|f(z)\| \mid \|z\| = r\}$
-/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/--
Erdős Problem 227 (Disproved):
Let $f = \sum a_n z^n$ be an entire function which is not a polynomial. Is it true that if
$$\lim_{r \to \infty} \frac{\max_n |a_n| r^n}{\max_{|z|=r} |f(z)|}$$
exists then it must be $0$?

This was disproved by Clunie and Hayman [ClHa64], who showed that the limit can take
any value in $[0, 1/2]$.
-/
@[category research solved, AMS 30]
theorem erdos_227 : answer(False) ↔
    ∀ (f : ℂ → ℂ) (a : ℕ → ℂ),
      (∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) →
      (∀ N : ℕ, ∃ n, N < n ∧ a n ≠ 0) →
      ∀ L : ℝ, Tendsto (fun r => maxTerm a r / maxModulus f r) atTop (𝓝 L) →
      L = 0 := by
  sorry

/--
Clunie (unpublished) proved that when all coefficients are non-negative ($a_n \geq 0$),
the original statement does hold: the limit must be $0$.
-/
@[category research solved, AMS 30]
theorem erdos_227_nonneg_coefficients :
    ∀ (f : ℂ → ℂ) (a : ℕ → ℂ),
      (∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) →
      (∀ N : ℕ, ∃ n, N < n ∧ a n ≠ 0) →
      (∀ n, 0 ≤ (a n).re ∧ (a n).im = 0) →
      ∀ L : ℝ, Tendsto (fun r => maxTerm a r / maxModulus f r) atTop (𝓝 L) →
      L = 0 := by
  sorry

/--
Clunie and Hayman [ClHa64] showed that the limit of the ratio of the maximum term to the
maximum modulus can take any value in $[0, 1/2]$.
-/
@[category research solved, AMS 30]
theorem erdos_227_achievable_values :
    ∀ L ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∃ (f : ℂ → ℂ) (a : ℕ → ℂ),
        (∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) ∧
        (∀ N : ℕ, ∃ n, N < n ∧ a n ≠ 0) ∧
        Tendsto (fun r => maxTerm a r / maxModulus f r) atTop (𝓝 L) := by
  sorry

end Erdos227
