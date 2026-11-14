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
# The irrationality exponent of log(3 + 2 sqrt(2))/sqrt(2)

The normalized value $\log(3+2\sqrt{2})/\sqrt{2}$ is irrational and has
irrationality exponent $2$. We state irrationality and the eventual
approximation bound directly.

*Reference:* Ryan Matthew Casper, *Irrationality exponent two for a normalized
real quadratic logarithm*, preprint with Lean formalization, October 7, 2026,
Section 1.
[Preprint](https://github.com/Mattie/math/blob/3f4e514444214e562eababb4eecc5b6ffb818002/preprints/The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026/paper.pdf).
-/

@[expose] public section

namespace NormalizedLogarithm

/-- The value $\log(3+2\sqrt{2})/\sqrt{2}$ is irrational. For every $\nu>2$,
there is an integer threshold $Q\ge2$ such that
$q^{-\nu}\le|\log(3+2\sqrt{2})/\sqrt{2}-p/q|$ for all integers $p,q$ with $q\ge Q$. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/Mattie/math/blob/3f4e514444214e562eababb4eecc5b6ffb818002/preprints/The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026/lean/RealNorm/FormalConjectures.lean#L14-L23"]
theorem normalized_log_sqrt_two_irrationality_and_bound :
    Irrational (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) ∧
      ∀ nu : ℝ, 2 < nu →
        ∃ Q : ℤ, 2 ≤ Q ∧
          ∀ p q : ℤ, Q ≤ q →
            (q : ℝ) ^ (-nu) ≤
              |Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 - (p : ℝ) / (q : ℝ)| := by
  sorry

end NormalizedLogarithm
