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
# Erdős Problem 223

*Reference:* [erdosproblems.com/223](https://www.erdosproblems.com/223)

Let $d \geq 2$ and $n \geq 2$. Let $f_d(n)$ be maximal such that there exists
some set of $n$ points $A \subseteq \mathbb{R}^d$, with diameter $1$, in which
the distance $1$ occurs between $f_d(n)$ many pairs of points in $A$.
Estimate $f_d(n)$.

Originally a conjecture of Vázsonyi [Er46b].

Known results:
- Hopf and Pannwitz [HoPa34] proved $f_2(n) = n$.
- Grünbaum [Gr56], Heppes [He56], and Strasziewicz [St57] showed $f_3(n) = 2n - 2$.
- Erdős [Er60b] proved that for $d \geq 4$,
  $f_d(n) = \left(\frac{p-1}{2p} + o(1)\right) n^2$ where $p = \lfloor d/2 \rfloor$.
- Swanepoel [Sw09] gave exact values for all $d \geq 4$ and sufficiently large $n$.

Related problems: #132, #1084.

## References

[Er46b] Erdős, P., _On sets of distances of n points_, American Mathematical Monthly (1946),
248–250.

[Er57] Erdős, P., _Some unsolved problems_, 1957.

[Er60b] Erdős, P., _On sets of distances of n points in Euclidean space_, Magyar Tudományos
Akadémia Matematikai Kutatóintézet Közleményei (1960), 165–169.

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975, p. 102.

[Gr56] Grünbaum, B., _A proof of Vázsonyi's conjecture_, Bulletin of the Research Council
of Israel, Section A (1956), 77–78.

[He56] Heppes, A., _Beweis einer Vermutung von A. Vázsonyi_, Acta Mathematica Academiae
Scientiarum Hungaricae (1956), 463–466.

[HoPa34] Hopf, H., Pannwitz, E., _Aufgabe 167_, Jahresbericht der Deutschen
Mathematiker-Vereinigung (1934), 114.

[St57] Straszewicz, S., _Sur un problème géométrique de P. Erdős_, Bulletin of the Polish
Academy of Sciences, Class III (1957), 39–40.

[Sw09] Swanepoel, K. J., _Unit distances and diameters in Euclidean spaces_, Discrete &
Computational Geometry (2009), 1–27.
-/

open Classical
open scoped EuclideanGeometry

namespace Erdos223

/--
Erdős Problem 223 ($d \geq 4$), upper bound — Erdős [Er60b]:
For $d \geq 4$, let $p = \lfloor d/2 \rfloor$. For every $\varepsilon > 0$, for sufficiently
large $n$, any $n$ points in $\mathbb{R}^d$ of diameter $\leq 1$ have at most
$\left(\frac{p-1}{2p} + \varepsilon\right) n^2$ unit-distance pairs.
-/
@[category research solved, AMS 52]
theorem erdos_223 (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (A : Finset (ℝ^ d)),
      N₀ ≤ A.card →
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) →
      let p := d / 2
      (unitDistNum A : ℝ) ≤
        ((↑p - 1) / (2 * ↑p) + ε) * (A.card : ℝ) ^ 2 := by
  sorry

/--
Erdős Problem 223 ($d \geq 4$), lower bound — Erdős [Er60b]:
For $d \geq 4$, let $p = \lfloor d/2 \rfloor$. For every $\varepsilon > 0$, for sufficiently
large $n$, there exist $n$ points in $\mathbb{R}^d$ of diameter $\leq 1$ with at least
$\left(\frac{p-1}{2p} - \varepsilon\right) n^2$ unit-distance pairs.
-/
@[category research solved, AMS 52]
theorem erdos_223.variants.d_ge4_lower (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ A : Finset (ℝ^ d),
        A.card = n ∧
        (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
        let p := d / 2
        ((↑p - 1) / (2 * ↑p) - ε) * (n : ℝ) ^ 2 ≤ (unitDistNum A : ℝ) := by
  sorry

/--
Erdős Problem 223 ($d = 2$), Hopf–Pannwitz [HoPa34]:
Among $n$ points in $\mathbb{R}^2$ with all pairwise distances $\leq 1$, the distance $1$
occurs between at most $n$ pairs.
-/
@[category research solved, AMS 52]
theorem erdos_223.variants.d2_upper (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    unitDistNum A ≤ A.card := by
  sorry

/--
Erdős Problem 223 ($d = 2$), tightness:
For every $n \geq 3$, there exist $n$ points in $\mathbb{R}^2$ with diameter $1$ and
exactly $n$ pairs at distance $1$.
-/
@[category research solved, AMS 52]
theorem erdos_223.variants.d2_tight (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n ∧
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
      unitDistNum A = n := by
  sorry

/--
Erdős Problem 223 ($d = 3$), Grünbaum–Heppes–Strasziewicz [Gr56, He56, St57]:
Among $n \geq 2$ points in $\mathbb{R}^3$ with all pairwise distances $\leq 1$, the distance $1$
occurs between at most $2n - 2$ pairs.
-/
@[category research solved, AMS 52]
theorem erdos_223.variants.d3_upper (A : Finset (EuclideanSpace ℝ (Fin 3)))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hcard : 2 ≤ A.card) :
    unitDistNum A ≤ 2 * A.card - 2 := by
  sorry

/--
Erdős Problem 223 ($d = 3$), tightness:
For every $n \geq 2$, there exist $n$ points in $\mathbb{R}^3$ with diameter $1$ and
exactly $2n - 2$ pairs at distance $1$.
-/
@[category research solved, AMS 52]
theorem erdos_223.variants.d3_tight (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 3)),
      A.card = n ∧
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
      unitDistNum A = 2 * n - 2 := by
  sorry

end Erdos223
