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
# Erdős Problem 588

*References:*
- [erdosproblems.com/588](https://www.erdosproblems.com/588)
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [Er84] Erdős, P., *Research problems*. Period. Math. Hungar. (1984), 101-103.
- [FuPa84] Füredi, Z. and Palásti, I., *Arrangements of lines with a large number of
  triangles*. Proc. Amer. Math. Soc. (1984), 561-566.
- [Gr76] Grünbaum, Branko, *New views on some old questions of combinatorial geometry*.
  Colloquio Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo I (1976), 451-468.
- [Ka63] Kárteszi, F., *Sylvester egy tételéről és Erdős egy sejtéséről*. Matematikai Lapok
  (1963), 3-10.
- [SoSt13] Solymosi, József and Stojaković, Miloš, *Many collinear $k$-tuples with no $k+1$
  collinear points*. Discrete Comput. Geom. (2013), 811-820.
-/

@[expose] public section

open EuclideanGeometry Filter Asymptotics

namespace Erdos588

/--
The set of lines in $\mathbb{R}^2$ containing exactly $k$ points from a given set $S$.

Only lines through two distinct points of $S$ are considered, so a line with fewer than two
points of $S$ is never counted.
-/
noncomputable def linesWithPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | (↑L ∩ S).ncard = k }

/--
`numLinesWithPointsMax k n` is $f_k(n)$: the maximum number of lines containing exactly $k$
points among all sets $S$ of $n$ points in $\mathbb{R}^2$ with no $k + 1$ points on a line.

Since $S$ has no $k + 1$ points on a line, the lines with at least $k$ points of $S$ are exactly
the lines with exactly $k$ points of $S$. The definition follows Erdős Problem 101 (the case
$k = 4$).
-/
noncomputable def numLinesWithPointsMax (k n : ℕ) : ℕ :=
  sSup {((linesWithPointsFor k S).ncard) | (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor (k + 1) S)}

/--
Let $f_k(n)$ be minimal such that if $n$ points in $\mathbb{R}^2$ have no $k+1$ points on a line
then there must be at most $f_k(n)$ many lines containing at least $k$ points. Is it true that
$$f_k(n) = o(n^2)$$
for $k \geq 4$?

The case $k = 4$ is Erdős Problem 101. The restriction $k \geq 4$ is needed: see
`Erdos588.erdos_588.variants.three_not_isLittleO`.
-/
@[category research open, AMS 52]
theorem erdos_588 : answer(sorry) ↔
    ∀ k : ℕ, 4 ≤ k →
      (fun n : ℕ ↦ (numLinesWithPointsMax k n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  sorry

/--
The trivial upper bound, by counting pairs of points: for $k \geq 2$,
$$f_k(n) \cdot k(k-1) \leq n(n-1).$$
-/
@[category textbook, AMS 52]
theorem erdos_588.variants.trivial_upper (k n : ℕ) (hk : 2 ≤ k) :
    numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1) := by
  sorry

/--
Sylvester showed (see [BGS74]) that
$$f_3(n) = \frac{n^2}{6} + O(n).$$

The upper bound $f_3(n) \leq n(n-1)/6$ is `Erdos588.erdos_588.variants.trivial_upper` with
$k = 3$. The lower bound comes from a construction on a cubic curve.
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.sylvester :
    (fun n : ℕ ↦ (numLinesWithPointsMax 3 n : ℝ) - (n : ℝ) ^ 2 / 6) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  sorry

/--
Burr, Grünbaum, and Sloane [BGS74] and Füredi and Palásti [FuPa84] gave constructions which
show that
$$f_3(n) \geq \left(\frac{1}{6} + o(1)\right) n^2.$$
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.three_lower :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 / 6 - ε) * (n : ℝ) ^ 2 ≤ (numLinesWithPointsMax 3 n : ℝ) := by
  sorry

/--
The restriction to $k \geq 4$ in `Erdos588.erdos_588` is necessary: $f_3(n)$ is not $o(n^2)$.
This follows from `Erdos588.erdos_588.variants.sylvester`.
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.three_not_isLittleO :
    ¬ (fun n : ℕ ↦ (numLinesWithPointsMax 3 n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  sorry

/--
Kárteszi [Ka63] proved that for $k \geq 4$,
$$f_k(n) \gg_k n \log n,$$
resolving a conjecture of Erdős that $f_k(n)/n \to \infty$.
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.karteszi :
    ∀ k : ℕ, 4 ≤ k → ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) * Real.log (n : ℝ) ≤ (numLinesWithPointsMax k n : ℝ) := by
  sorry

/--
Grünbaum [Gr76] proved that for $k \geq 4$,
$$f_k(n) \gg_k n^{1 + \frac{1}{k-2}}.$$
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.grunbaum :
    ∀ k : ℕ, 4 ≤ k → ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ (1 + 1 / ((k : ℝ) - 2)) ≤ (numLinesWithPointsMax k n : ℝ) := by
  sorry

/--
Solymosi and Stojaković [SoSt13] proved that for $k \geq 4$,
$$f_k(n) \gg_k n^{2 - O_k(1/\sqrt{\log n})}.$$
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.solymosi_stojakovic :
    ∀ k : ℕ, 4 ≤ k → ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ (2 - C / Real.sqrt (Real.log (n : ℝ))) ≤
        (numLinesWithPointsMax k n : ℝ) := by
  sorry

/--
Erdős speculated that Grünbaum's bound $n^{1 + \frac{1}{k-2}}$ may be the correct order of
magnitude of $f_k(n)$ for $k \geq 4$. This is false: by
`Erdos588.erdos_588.variants.solymosi_stojakovic` [SoSt13], for every $k \geq 4$ we have
$f_k(n) \neq O(n^{1 + \frac{1}{k-2}})$.
-/
@[category research solved, AMS 52]
theorem erdos_588.variants.grunbaum_order :
    ∀ k : ℕ, 4 ≤ k →
      ¬ (fun n : ℕ ↦ (numLinesWithPointsMax k n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 + 1 / ((k : ℝ) - 2))) := by
  sorry

end Erdos588
