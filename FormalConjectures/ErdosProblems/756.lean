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
# Erdős Problem 756

*References:*
- [erdosproblems.com/756](https://www.erdosproblems.com/756)
- [Bh24] Bhowmick, K., *A problem of Erdős about rich distances*. arXiv:2407.01174 (2024).
- [CDL25] Clemen, F., Dumitrescu, A. and Liu, D., *On multiplicities of interpoint distances*.
  arXiv:2505.04283 (2025).
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*.
  Discrete Math. (1997), 227-231.
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
  Combinatorica (1990), 261-269.
- [HoPa34] Hopf, H. and Pannwitz, E., *Aufgabe 167*. Jber. Deutsch. Math. Verein. (1934), 114.
-/

open Filter
open scoped EuclideanGeometry Asymptotics

namespace Erdos756

/-- The number of unordered pairs of distinct points of `A` which are at distance exactly `d`.
The division by two accounts for `Finset.offDiag` listing each unordered pair twice. -/
noncomputable def distanceMultiplicity (A : Finset ℝ²) (d : ℝ) : ℕ :=
  (A.offDiag.filter fun pair : ℝ² × ℝ² => dist pair.1 pair.2 = d).card / 2

/-- The distances determined by `A` which occur for at least `k` many pairs of points of `A`. -/
noncomputable def richDistances (A : Finset ℝ²) (k : ℕ) : Finset ℝ :=
  (A.offDiag.image fun pair : ℝ² × ℝ² => dist pair.1 pair.2).filter
    fun d => k ≤ distanceMultiplicity A d

/-- The largest number of distinct distances that a set of `n` points in $\mathbb{R}^2$ can
determine, each of which occurs for more than `n` many pairs of points of the set. -/
noncomputable def maxRichDistances (n : ℕ) : ℕ :=
  sSup {(richDistances A (n + 1)).card | (A : Finset ℝ²) (_ : A.card = n)}

/--
Let $A\subset \mathbb{R}^2$ be a set of $n$ points. Can there be $\gg n$ many distinct distances
each of which occurs for more than $n$ many pairs from $A$?

The answer is yes: Bhowmick [Bh24] constructs a set of $n$ points in $\mathbb{R}^2$ such that
$\lfloor\frac{n}{4}\rfloor$ distances occur at least $n+1$ times.
-/
@[category research solved, AMS 52]
theorem erdos_756 : answer(True) ↔
    (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (maxRichDistances n : ℝ)) := by
  sorry

/--
Bhowmick [Bh24] constructs a set of $n$ points in $\mathbb{R}^2$ such that
$\lfloor\frac{n}{4}\rfloor$ distances occur at least $n+1$ times.
-/
@[category research solved, AMS 52]
theorem erdos_756.variants.bhowmick (n : ℕ) :
    ∃ A : Finset ℝ², A.card = n ∧ n / 4 ≤ (richDistances A (n + 1)).card := by
  sorry

/--
More generally, they construct, for any $m$ and large $n$, a set of $n$ points such that
$\lfloor \frac{n}{2(m+1)}\rfloor$ distances occur at least $n+m$ times.
-/
@[category research solved, AMS 52]
theorem erdos_756.variants.bhowmick_general (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℝ², A.card = n ∧
      n / (2 * (m + 1)) ≤ (richDistances A (n + m)).card := by
  sorry

end Erdos756
