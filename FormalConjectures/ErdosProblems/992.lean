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
import FormalConjecturesForMathlib.NumberTheory.Lacunary

/-!
# Erdős Problem 992

*References:*
- [erdosproblems.com/992](https://www.erdosproblems.com/992)
- [Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
  (1964), 52–65.
- [ErKo49] Erdős, P. and Koksma, J. F., _On the uniform distribution modulo 1 of sequences_.
  Nederl. Akad. Wetensch., Proc. (1949), 851–854 = Indagationes Math. 11, 299–302.
- [Ca50] Cassels, J. W. S., _Some metrical theorems of Diophantine approximation. III_. Proc.
  Cambridge Philos. Soc. (1950), 219–225.
- [Ba81] Baker, R. C., _Metric number theory and the large sieve_. J. London Math. Soc. (2)
  (1981), 34–40.
- [BePh94] Berkes, I. and Philipp, W., _The size of trigonometric and Walsh series and uniform
  distribution mod 1_. J. London Math. Soc. (2) (1994), 454–464.

Let $x_1 < x_2 < \cdots$ be an infinite sequence of integers. Is it true that, for
almost all $\alpha \in [0,1]$, the discrepancy
$$D(N) = \max_{I \subseteq [0,1]} |\#\{n \le N : \{\alpha x_n\} \in I\} - |I| \cdot N|$$
satisfies $D(N) \ll N^{1/2} (\log N)^{o(1)}$? Or even $D(N) \ll N^{1/2} (\log \log N)^{O(1)}$?

Erdős and Koksma [ErKo49] and Cassels [Ca50] independently proved that, for any
sequence $x_i$ and almost all $\alpha$, $D(N) \ll N^{1/2} (\log N)^{5/2 + o(1)}$. Baker [Ba81]
improved this to $D(N) \ll N^{1/2} (\log N)^{3/2 + o(1)}$.

Erdős and Gál (unpublished) proved that for lacunary sequences (where
$x_{i+1}/x_i > \lambda > 1$ for all $i$), the stronger bound
$D(N) \ll N^{1/2} (\log \log N)^{O(1)}$ holds for almost all $\alpha$.

This was disproved (for general sequences) by Berkes and Philipp [BePh94], who
constructed a sequence of integers $x_1 < x_2 < \cdots$ such that, for almost all
$\alpha \in [0,1]$,
$$\limsup_{N \to \infty} D(N) / (N \log N)^{1/2} > 0.$$
-/

open Filter MeasureTheory Finset

namespace Erdos992

/-- The discrepancy of the sequence $\{\alpha \cdot x(n)\} \pmod{1}$ with respect to
subintervals of $[0,1)$.
$$D(N) = \sup_{0 \le a < b \le 1} |\#\{n < N : \{\alpha \cdot x(n)\} \in [a, b)\} - (b - a) \cdot N|$$ -/
noncomputable def discrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
    d = abs (((Finset.range N).filter (fun n =>
      a ≤ Int.fract (α * (x n : ℝ)) ∧ Int.fract (α * (x n : ℝ)) < b)).card -
      (b - a) * (N : ℝ))}

/--
Erdős Problem 992 (disproved by Berkes and Philipp [BePh94]):

Is it true that for every strictly increasing sequence of positive integers
$x_1 < x_2 < \cdots$ and almost all $\alpha \in [0,1]$, the discrepancy satisfies
$D(N) \ll N^{1/2} (\log N)^{o(1)}$?

Here $D(N) \ll N^{1/2} (\log N)^{o(1)}$ is formalized as: for every $\varepsilon > 0$,
there exists $C > 0$ such that $D(N) \le C \sqrt{N} (\log N)^\varepsilon$ for all
sufficiently large $N$.
-/
@[category research solved, AMS 11 28]
theorem erdos_992 : answer(False) ↔
    ∀ (x : ℕ → ℤ), StrictMono x → (∀ n, 0 < x n) →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ ε : ℝ, ε > 0 →
        ∃ C : ℝ, C > 0 ∧
          ∀ᶠ N in atTop,
            discrepancy x α N ≤
              C * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ ε := by
  sorry

/--
Erdős Problem 992, stronger variant (also disproved by [BePh94]):

Is it true that $D(N) \ll N^{1/2} (\log \log N)^{O(1)}$? Here this is formalized as:
there exist $C > 0$ and $K > 0$ such that $D(N) \le C \sqrt{N} (\log \log N)^K$ for
all sufficiently large $N$.
-/
@[category research solved, AMS 11 28]
theorem erdos_992.variants.stronger : answer(False) ↔
    ∀ (x : ℕ → ℤ), StrictMono x → (∀ n, 0 < x n) →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∃ C : ℝ, C > 0 ∧ ∃ K : ℝ, K > 0 ∧
        ∀ᶠ N in atTop,
          discrepancy x α N ≤
            C * Real.sqrt (N : ℝ) *
              (Real.log (Real.log (N : ℝ))) ^ K := by
  sorry

/--
Berkes and Philipp [BePh94] disproved Erdős Problem 992 by constructing a
strictly increasing sequence of positive integers such that for almost all
$\alpha \in [0,1]$,
$$\limsup_{N \to \infty} D(N) / (N \log N)^{1/2} > 0.$$
-/
@[category research solved, AMS 11 28]
theorem erdos_992.variants.berkes_philipp :
    ∃ (x : ℕ → ℤ), StrictMono x ∧ (∀ n, 0 < x n) ∧
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∃ c : ℝ, c > 0 ∧
        ∃ᶠ N in atTop,
          discrepancy x α N ≥
            c * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by
  sorry

/--
Erdős–Gál (unpublished): for lacunary sequences (where $x_{i+1}/x_i > \lambda > 1$),
the stronger bound $D(N) \ll N^{1/2} (\log \log N)^{O(1)}$ holds for almost all
$\alpha \in [0,1]$. Here this is formalized as: there exist $C > 0$ and $K > 0$
such that $D(N) \le C \sqrt{N} (\log \log N)^K$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11 28]
theorem erdos_992.variants.erdos_gal :
    ∀ (x : ℕ → ℕ), IsLacunary x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∃ C : ℝ, C > 0 ∧ ∃ K : ℝ, K > 0 ∧
        ∀ᶠ N in atTop,
          discrepancy (fun n => (x n : ℤ)) α N ≤
            C * Real.sqrt (N : ℝ) *
              (Real.log (Real.log (N : ℝ))) ^ K := by
  sorry

end Erdos992
