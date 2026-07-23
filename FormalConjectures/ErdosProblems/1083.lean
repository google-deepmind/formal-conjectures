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

import FormalConjecturesUtil

/-!
# Erdős Problem 1083

*References:*
- [erdosproblems.com/1083](https://www.erdosproblems.com/1083)
- [Er46b] Erdős, P., On sets of distances of $n$ points. Amer. Math. Monthly (1946), 248--250.
- [CEGSW90] Clarkson, Kenneth L. and Edelsbrunner, Herbert and Guibas, Leonidas J. and Sharir,
  Micha and Welzl, Emo, Combinatorial complexity bounds for arrangements of curves and spheres.
  Discrete Comput. Geom. (1990), 99--160.
- [APST04] Aronov, Boris and Pach, János and Sharir, Micha and Tardos, Gábor, Distinct distances
  in three and higher dimensions. Combin. Probab. Comput. (2004), 283--293.
- [SoVu08] Solymosi, József and Vu, Van H., Near optimal bounds for the Erdős distinct distances
  problem in high dimensions. Combinatorica (2008), 113--125.
-/

open Filter
open scoped Topology Finset

namespace Erdos1083

/--
The number of distinct distances determined by a finite set of points in $\mathbb{R}^d$.
This is the `d`-dimensional analogue of `EuclideanGeometry.distinctDistances`.
-/
noncomputable def distinctDistances {d : ℕ} (points : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  #(points.offDiag.image fun pair => dist pair.1 pair.2)

/--
$f_d(n)$: the minimal number of distinct distances determined by any set of $n$ points
in $\mathbb{R}^d$. This is the `d`-dimensional analogue of
`EuclideanGeometry.minimalDistinctDistances`.
-/
noncomputable def minimalDistinctDistances (d n : ℕ) : ℕ :=
  sInf {distinctDistances points |
    (points : Finset (EuclideanSpace ℝ (Fin d))) (_ : points.card = n)}

/--
**Erdős Problem 1083.**
Let $d\geq 3$, and let $f_d(n)$ be the minimal $m$ such that every set of $n$ points in
$\mathbb{R}^d$ determines at least $m$ distinct distances.
Estimate $f_d(n)$ - in particular, is it true that $f_d(n)=n^{\frac{2}{d}-o(1)}?$?
-/
@[category research open, AMS 5 52]
theorem erdos_1083 : answer(sorry) ↔ ∀ d : ℕ, 3 ≤ d →
    Tendsto (fun n : ℕ => Real.log (minimalDistinctDistances d n) / Real.log n)
      atTop (𝓝 (2 / (d : ℝ))) := by
  sorry

/--
Erdős [Er46b] proved $f_d(n) \ll_d n^{2/d}$.
-/
@[category research solved, AMS 5 52]
theorem variants.grid_upper_bound (d : ℕ) (hd : 3 ≤ d) :
    (minimalDistinctDistances d · : ℕ → ℝ) =O[atTop] (· ^ (2 / (d : ℝ)) : ℕ → ℝ) := by
  sorry

/--
Erdős [Er46b] proved the lower bound $n^{1/d} \ll_d f_d(n)$.
-/
@[category research solved, AMS 5 52]
theorem variants.erdos_lower_bound (d : ℕ) (hd : 3 ≤ d) :
    (· ^ (1 / (d : ℝ)) : ℕ → ℝ) =O[atTop] (minimalDistinctDistances d · : ℕ → ℝ) := by
  sorry

/--
Clarkson, Edelsbrunner, Guibas, Sharir, and Welzl [CEGSW90] proved $f_3(n) \gg n^{1/2}$.
-/
@[category research solved, AMS 5 52]
theorem variants.lower_bound_cegsw :
    (· ^ (1 / 2 : ℝ) : ℕ → ℝ) =O[atTop] (minimalDistinctDistances 3 · : ℕ → ℝ) := by
  sorry

/--
Aronov, Pach, Sharir, and Tardos [APST04] in Corollary 1.3 proved
$f_d(n) \gg n^{\frac{1}{d - 90/77} - o(1)}$ for any $d \geq 3$.
-/
@[category research solved, AMS 5 52]
theorem variants.lower_bound_apst (d : ℕ) (hd : 3 ≤ d) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / ((d : ℝ) - 90 / 77) - ε) ≤ minimalDistinctDistances d n := by
  sorry

/--
Solymosi and Vu [SoVu08] in Theorem 1.1 proved $f_d(n) \gg_d n^{\frac{2}{d} - \frac{2}{d(d+2)}}$,
for $d \geq 3$.
-/
@[category research solved, AMS 5 52]
theorem variants.lower_bound_solymosi_vu (d : ℕ) (hd : 3 ≤ d) :
    ((· : ℕ → ℝ) ^ (2 / (d : ℝ) - 2 / ((d : ℝ) * ((d : ℝ) + 2)))) =O[atTop]
      (minimalDistinctDistances d · : ℕ → ℝ) := by
  sorry

/--
Solymosi and Vu [SoVu08, Corollary 1.2] proved $f_3(n) \gg n^{0.5643}$.
-/
@[category research solved, AMS 5 52]
theorem variants.lower_bound_solymosi_vu_dim_three :
    (· ^ (0.5643 : ℝ) : ℕ → ℝ) =O[atTop] ((minimalDistinctDistances 3 ·) : _ → ℝ) := by
  sorry

end Erdos1083
