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

*References:* 
- [erdosproblems.com/1050](https://www.erdosproblems.com/1050)
- [Bo91] Borwein, Peter B., On the irrationality of {$\sum(1/(q^n+r))$}. J. Number Theory (1991), 253--259.
- [Bo92] Borwein, Peter B., On the irrationality of certain series. Math. Proc. Camb. Phil. Soc. (1992), 141--146.
- [Er48] Erdős, P., On arithmetical properties of Lambert series. J. Indian Math. Soc. (N.S.) (1948), 63-66.
- [Er88c] Erdős, P., On the irrationality of certain series: problems and results. New advances in transcendence theory (Durham, 1986) (1988), 102-109.

Is $\sum_{n=1}^\infty \frac{1}{2^n - 3}$ irrational?

The answer is **yes**, proved by P. B. Borwein [Bo91] (with a cleaner self-contained proof in [Bo92]),
specialized to $q = 2$, $r = -3$.

A formal Lean proof is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code and Harmonic's Aristotle.
-/

namespace Erdos1050

/-- **Erdős Problem 1050.** The series $\sum_{n=1}^\infty \frac{1}{2^n - 3}$ is irrational.

The source sum runs over $n \ge 1$; as a `tsum` over `ℕ` (which starts at $0$) it is reindexed
$n \mapsto n + 1$, i.e. $\sum_{n=0}^\infty 1/(2^{n+1} - 3)$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos1050/Statement.lean"]
theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
  sorry

/-- **Erdős Problem 1050, variant [Er48].** Erdős proved that the related series
$\sum_{n=1}^\infty \frac{1}{2^n - 1}$ (which equals the Lambert series $\sum_n \frac{\tau(n)}{2^n}$,
where $\tau$ is the divisor function) is irrational. This is the $q = 2$, $r = -1$ case of Borwein's
general theorem `Erdos1050.erdos_1050.variants.borwein` below. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos1050/Variants.lean"]
theorem erdos_1050.variants.two_pow_sub_one :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) := by
  sorry

/-- **Erdős Problem 1050, variant [Bo91].** Borwein's general theorem: for every integer $q \ge 2$
and rational $r \ne 0$ with $r \ne -q^n$ for all $n \ge 1$, the series $\sum_{n=1}^\infty \frac{1}{q^n + r}$
is irrational. Problem 1050 is the case $q = 2$, $r = -3$; the [Er48] variant is $q = 2$, $r = -1$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos1050/Variants.lean"]
theorem erdos_1050.variants.borwein (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) := by
  sorry

/-- **Erdős Problem 1050, variant [Er88c] (open).** Erdős conjectured that
$\sum_{n=1}^\infty \frac{1}{2^n + t}$ is *transcendental* for every integer $t \ne 0$ — strictly
stronger than the irrationality established by Borwein [Bo91]. This remains open.

Two exclusions make the series well-posed and the claim non-vacuous, exactly as in Borwein's theorem:
$t \ne -2^n$ for all $n \ge 1$ (so no denominator vanishes), and $t \ne 0$ (at $t = 0$ the series is
the rational $\sum_{n \ge 1} 2^{-n} = 1$, hence not transcendental). -/
@[category research open, AMS 11]
theorem erdos_1050.variants.transcendental :
    answer(sorry) ↔
      ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
        Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + (t : ℝ))) := by
  sorry

end Erdos1050
