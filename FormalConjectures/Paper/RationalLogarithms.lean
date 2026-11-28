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
# The irrationality exponent of positive rational logarithms

For every positive rational $a \ne 1$, the natural logarithm $\log a$ is irrational
and has irrationality exponent $2$ [Cas26, Section 1]. We state the uniform
approximation bound directly: for each $\varepsilon > 0$, every sufficiently large
denominator $q$ satisfies $|\log a - p/q| \ge q^{-(2+\varepsilon)}$ for all integers $p$.
Together with irrationality and Dirichlet's theorem, this gives the exponent $2$.

*Reference:* [Cas26] Ryan Matthew Casper, *The irrationality exponent of positive
rational logarithms is 2*, preprint with Lean formalization (2026), Section 1.
[Published manuscript and source](https://github.com/Mattie/math/tree/0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd/preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026).
-/

@[expose] public section

namespace RationalLogarithms

/-- For $a \in \mathbb{Q}$ with $a > 0$ and $a \ne 1$, the natural logarithm $\log a$
is irrational. For every $\varepsilon > 0$, there is a threshold $Q \ge 2$, depending
on $a$ and $\varepsilon$, such that $q^{-(2+\varepsilon)} \le |\log a-p/q|$ for every
$p \in \mathbb{Z}$ and $q \in \mathbb{N}$ with $q \ge Q$. The case $a=1$ is excluded
because $\log 1=0$ is rational. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/Mattie/math/blob/0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd/preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/review/blind-statement/CertifiedBridge.lean#L5-L16"]
theorem rational_log_irrationality_and_bound (a : ℚ) (ha : 0 < a) (ha_ne_one : a ≠ 1) :
    Irrational (Real.log (a : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ Q : ℕ, 2 ≤ Q ∧
          ∀ (p : ℤ) (q : ℕ), Q ≤ q →
            Real.rpow (q : ℝ) (-(2 + ε)) ≤
              |Real.log (a : ℝ) - (p : ℝ) / (q : ℝ)| := by
  sorry

end RationalLogarithms
