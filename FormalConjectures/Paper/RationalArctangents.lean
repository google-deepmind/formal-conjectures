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
# The irrationality exponent of nonzero rational arctangents

For every nonzero rational $r$, the principal arctangent $\arctan r$, measured in
radians, is irrational and has irrationality exponent $2$ [Cas26, Section 1].
We state irrationality together with the eventual approximation bound directly.

*Reference:* [Cas26] Ryan Matthew Casper, *The irrationality exponent of nonzero
rational arctangents is 2*, preprint with Lean formalization, October 7, 2026,
Sections 1 and 8.
-/

@[expose] public section

namespace RationalArctangents

/-- For $r \in \mathbb{Q}$ with $r \ne 0$, the principal arctangent $\arctan r$
in radians is irrational. For every $\nu > 2$, there is an integer threshold
$Q \ge 2$, depending on $r$ and $\nu$, such that $q^{-\nu} \le |\arctan r-p/q|$
for all $p,q \in \mathbb{Z}$ with $q \ge Q$. The case $r=0$ is excluded because
$\arctan 0=0$ is rational. -/
@[category research solved, AMS 11]
theorem rational_arctan_irrationality_and_bound (r : ℚ) (hr : r ≠ 0) :
    Irrational (Real.arctan (r : ℝ)) ∧
      ∀ nu : ℝ, 2 < nu →
        ∃ Q : ℤ, 2 ≤ Q ∧
          ∀ p q : ℤ, Q ≤ q →
            (q : ℝ) ^ (-nu) ≤ |Real.arctan (r : ℝ) - (p : ℝ) / (q : ℝ)| := by
  sorry

end RationalArctangents
