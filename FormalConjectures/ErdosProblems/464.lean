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
# Erdős Problem 464

For any lacunary sequence of natural numbers (where the ratio of consecutive terms is bounded
away from 1), there exists an irrational number θ such that the sequence of distances from
θ·nₖ to the nearest integer is not dense in [0, 1/2].

Proved independently by de Mathan and Pollington. Peres and Schlag proved the quantitative
strengthening that $\inf_{k \geq 1} \|\theta n_k\| \gg \varepsilon / \log(1/\varepsilon)$.

## References

* [dM80] de Mathan, B., _Numbers contravening a condition in density modulo 1_.
  Acta Math. Acad. Sci. Hungar. (1980), 237–241.
* [Po79b] Pollington, A. D., _On the density of sequence {nₖξ}_.
  Illinois J. Math. (1979), 511–515.
* [Ka01] Katznelson, Y., _Chromatic numbers of Cayley graphs on Z and recurrence_.
  Combinatorica (2001), 211–219.
* [AkMo04] Akhunzhanov, R. K. and Moshchevitin, N. G.,
  _On the chromatic number of a distance graph associated with a lacunary sequence_.
  Dokl. Akad. Nauk (2004), 295–296.
* [Du06] Dubickas, A., _On the fractional parts of lacunary sequences_.
  Math. Scand. (2006), 136–146.
* [PeSc10] Peres, Y. and Schlag, W.,
  _Two Erdős problems on lacunary sequences: chromatic number and Diophantine approximation_.
  Bull. Lond. Math. Soc. (2010), 295–300.

See also Problem 894.

*Reference:* [erdosproblems.com/464](https://www.erdosproblems.com/464)
-/

namespace Erdos464

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
A sequence $a : \mathbb{N} \to \mathbb{N}$ is lacunary if it is strictly increasing and there
exists $\varepsilon > 0$ such that $a(k+1) \geq (1+\varepsilon) \cdot a(k)$ for all $k$.
-/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ ∃ ε : ℝ, ε > 0 ∧ ∀ k : ℕ, (a (k + 1) : ℝ) ≥ (1 + ε) * (a k : ℝ)

/--
Erdős Problem 464 (Proved by de Mathan and Pollington):

Let $A = \{n_1 < n_2 < \cdots\} \subset \mathbb{N}$ be a lacunary sequence (there exists
$\varepsilon > 0$ with $n_{k+1} \geq (1+\varepsilon)n_k$ for all $k$). Then there exists an
irrational $\theta$ such that $\{\| \theta n_k \| : k \geq 1\}$ is not dense in $[0, 1/2]$,
where $\|x\|$ denotes the distance from $x$ to the nearest integer.

The "not dense" condition is formalized as: there exist $0 \leq c < d \leq 1/2$ such that
$\|\theta n_k\| \notin (c, d)$ for all $k$, i.e., the image avoids some open subinterval
of $[0, 1/2]$.
-/
@[category research solved, AMS 11]
theorem erdos_464 :
    ∀ (a : ℕ → ℕ), IsLacunary a →
    ∃ θ : ℝ, Irrational θ ∧
      ∃ c d : ℝ, 0 ≤ c ∧ c < d ∧ d ≤ 1 / 2 ∧
        ∀ k : ℕ, distNearestInt (θ * ↑(a k)) ∉ Set.Ioo c d := by
  sorry

/--
Quantitative strengthening of Erdős Problem 464 (Peres–Schlag, 2010):

For any lacunary sequence with ratio parameter ε, there exists an irrational θ and a constant
C > 0 (independent of ε) such that $\inf_{k \geq 1} \|\theta n_k\| \geq C \cdot \varepsilon
/ \log(1/\varepsilon)$.
-/
@[category research solved, AMS 11]
theorem erdos_464_quantitative :
    ∃ C : ℝ, C > 0 ∧
    ∀ (a : ℕ → ℕ) (ε : ℝ), ε > 0 ∧ ε < 1 ∧
      StrictMono a ∧ (∀ k : ℕ, (a (k + 1) : ℝ) ≥ (1 + ε) * (a k : ℝ)) →
    ∃ θ : ℝ, Irrational θ ∧
      ∀ k : ℕ, distNearestInt (θ * ↑(a k)) ≥ C * ε / Real.log (1 / ε) := by
  sorry

end Erdos464
