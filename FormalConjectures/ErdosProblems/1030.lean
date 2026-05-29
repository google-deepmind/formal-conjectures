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
# Erdős Problem 1030

See also problems [544](https://www.erdosproblems.com/544) and
[1014](https://www.erdosproblems.com/1014).

OEIS: [A000791](https://oeis.org/A000791), [A059442](https://oeis.org/A059442).

*References:*
- [erdosproblems.com/1030](https://www.erdosproblems.com/1030)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333–350.
- [BEFS89] Burr, S.A., Erdős, P., Faudree, R.J., and Schelp, R.H.,
  _On the difference between consecutive Ramsey numbers_. Utilitas Math. (1989), 115–118.
-/

open Filter SimpleGraph

open scoped Topology

namespace Erdos1030

/--
Erdős Problem 1030 [Er93, p. 339]:

There exists $c > 0$ such that
$$
  \lim_{k \to \infty} \frac{R(k+1, k)}{R(k, k)} > 1 + c.
$$
-/
@[category research open, AMS 5]
theorem erdos_1030 :
    ∃ c L : ℝ, c > 0 ∧ L > 1 + c ∧
      Tendsto (fun k : ℕ =>
        (graphRamseyNumber (k + 1) k : ℝ) / (graphRamseyNumber k k : ℝ))
        atTop (nhds L) := by
  sorry

/--
Erdős Problem 1030 — eventually-larger variant [Er93, p. 339]:

There exists $c > 0$ such that eventually (for all sufficiently large $k$),
$R(k+1, k) / R(k, k) \geq 1 + c$. This is implied by the limit formulation, but
is itself open since the limit need not exist.
-/
@[category research open, AMS 5]
theorem erdos_1030.variants.eventually :
    ∃ c : ℝ, c > 0 ∧
    ∀ᶠ k : ℕ in atTop,
      (graphRamseyNumber (k + 1) k : ℝ) / (graphRamseyNumber k k : ℝ) ≥ 1 + c := by
  sorry

/--
Weaker variant of Erdős Problem 1030 [Er93, p. 339]:

There exists $c > 1$ such that $R(k+1,k) - R(k,k) > k^c$ for all sufficiently large $k$.

Erdős and Sós could not even prove this weaker statement.
-/
@[category research open, AMS 5]
theorem erdos_1030.variants.weak :
    ∃ c : ℝ, c > 1 ∧
    ∀ᶠ k : ℕ in atTop,
      (graphRamseyNumber (k + 1) k : ℝ) - (graphRamseyNumber k k : ℝ) > (k : ℝ) ^ c := by
  sorry

/--
Trivial bound: $R(k+1, k) - R(k, k) \geq k - 2$ for all $k \geq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_1030.variants.trivial_bound :
    ∀ k : ℕ, 2 ≤ k →
      (k : ℤ) - 2 ≤ (graphRamseyNumber (k + 1) k : ℤ) - (graphRamseyNumber k k : ℤ) := by
  sorry

/--
Burr–Erdős–Faudree–Schelp bound [BEFS89]: $R(k+1, k) - R(k, k) \geq 2k - 5$ for
all sufficiently large $k$.
-/
@[category research solved, AMS 5]
theorem erdos_1030.variants.burr_erdos_faudree_schelp :
    ∀ᶠ k : ℕ in atTop,
      (2 * (k : ℤ) - 5) ≤ (graphRamseyNumber (k + 1) k : ℤ) - (graphRamseyNumber k k : ℤ) := by
  sorry

end Erdos1030
