/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 89

*References:*
- [erdosproblems.com/89](https://www.erdosproblems.com/89)
- [Er46] P. Erdős, "On sets of distances of n points", Amer. Math. Monthly 53 (1946), 248–250.
- [GK15] L. Guth, N. H. Katz, "On the Erdős distinct distances problem in the plane",
  Annals of Mathematics 181 (2015), 155–190.

### AI disclosure
Lean 4 code in this file was drafted with assistance from Claude (Anthropic).
The mathematical content and formalization decisions are the author's own work.
-/

open Finset Real

namespace Erdos89

/-- Euclidean distance between two points in ℝ². -/
noncomputable def euclidDist (p q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  dist p q

/-- The set of distinct pairwise distances determined by a finite point set in ℝ². -/
noncomputable def distinctDistances (pts : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  pts.offDiag.image (fun pq => dist pq.1 pq.2)

/--
Let $x_1, \ldots, x_n$ be $n$ distinct points in $\mathbb{R}^2$. Let $f(n)$ denote the
minimum number of distinct distances determined by $n$ points. Is it true that
$f(n) \gg n / \sqrt{\log n}$?

A $\sqrt{n} \times \sqrt{n}$ integer grid shows that $f(n) \ll n / \sqrt{\log n}$
(via the Landau–Ramanujan theorem on sums of two squares), so this bound, if true,
would be best possible.

Guth and Katz [GK15] proved $f(n) \gg n / \log n$, which is the best known lower bound.
The conjectured bound $n / \sqrt{\log n}$ remains open — the gap is a factor of $\sqrt{\log n}$.
-/
@[category research open, AMS 52]
theorem erdos_89 :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
      2 ≤ pts.card →
        C * (pts.card : ℝ) / (Real.log (pts.card : ℝ)) ^ ((1 : ℝ) / 2 + ε) ≤
        (distinctDistances pts).card := by
  sorry

/--
Guth and Katz [GK15] proved that any $n$ points in $\mathbb{R}^2$ determine
$\gg n / \log n$ distinct distances. This is the best known lower bound toward
the full Erdős conjecture (which asks for $n / \sqrt{\log n}$).
-/
@[category research solved, AMS 52]
theorem erdos_89.variants.guth_katz :
    ∃ C > (0 : ℝ), ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
      2 ≤ pts.card →
        C * (pts.card : ℝ) / Real.log (pts.card : ℝ) ≤
        (distinctDistances pts).card := by
  sorry

/--
The integer lattice $\{1, \ldots, \lfloor\sqrt{n}\rfloor\}^2$ determines
$\Theta(n / \sqrt{\log n})$ distinct distances, by the Landau–Ramanujan theorem on
representations as sums of two squares. This shows the conjectured lower bound
is best possible up to constants.
-/
@[category research solved, AMS 52]
theorem erdos_89.variants.grid_upper_bound :
    ∃ C > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      ∃ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
        pts.card = n ∧
        (distinctDistances pts).card ≤ C * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  sorry

end Erdos89
