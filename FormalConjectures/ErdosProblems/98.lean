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
# Erdős Problem 98

*References:*
- [[Er75f](https://mathscinet.ams.org/mathscinet/relay-station?mr=411984)]
  Erdős, Paul, On some problems of elementary and combinatorial geometry.
  Ann. Mat. Pura Appl. (4) (1975), 99-108.
- [[Er83c](https://mathscinet.ams.org/mathscinet/relay-station?mr=706025)]
  Erdős, Paul, Combinatorial problems in geometry.
  Math. Chronicle (1983), 35-54.
- [[Er87b](https://mathscinet.ams.org/mathscinet/relay-station?mr=910710)]
  Erdős, P., Some combinatorial and metric problems in geometry.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [[Er90](https://mathscinet.ams.org/mathscinet/relay-station?mr=1117038)]
  Erdős, Paul, Some of my favourite unsolved problems.
  A tribute to Paul Erdős (1990), 467-478.
- [[Er92b](https://mathscinet.ams.org/mathscinet/relay-station?mr=1275857)]
  Erdős, Paul, Some of my favourite problems in various branches of combinatorics.
  Matematiche (Catania) (1992), 231-240.
- [[EFPR93](https://mathscinet.ams.org/mathscinet/relay-station?mr=1210096)]
  Erdős, Paul and Füredi, Zoltán and Pach, János and Ruzsa, Imre Z.,
  The grid revisited. Discrete Math. (1993), 189-196.
- [[Er94b](https://mathscinet.ams.org/mathscinet/relay-station?mr=1304854)]
  Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
  Math. Pannon. (1994), 261-269.
- [[Er97e](https://mathscinet.ams.org/mathscinet/relay-station?mr=1487304)]
  Erdős, Paul, Some of my favourite unsolved problems.
  Math. Japon. (1997), 527-537.
- [erdosproblems.com/98](https://www.erdosproblems.com/98)
-/

open Finset EuclideanGeometry Filter

namespace Erdos98

/-- $h(n)$ is the minimum number of distinct distances determined by any
$n$-point set in $\mathbb{R}^2$ in general position (no three collinear, no four
cocyclic). -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset ℝ², points.card = n ∧
    InGeneralPosition points ∧ k = distinctDistances points}

/--
Let $h(n)$ be such that any $n$ points in $\mathbb{R}^2$, with no three on a line
and no four on a circle, determine at least $h(n)$ distinct distances. Does
$h(n)/n\to \infty$?
-/
@[category research open, AMS 52]
theorem erdos_98 :
    answer(sorry) ↔ Tendsto (fun n : ℕ ↦ ((h n : ℝ) / (n : ℝ))) atTop atTop := by
  sorry

/--
Erdős could not even prove $h(n)\geq n$. Pach has shown $h(n) < n^{\log_2 3}$.
Erdős, Füredi, and Pach [EFPR93] have improved this to
$h(n) < n\exp(c\sqrt{\log n})$ for some constant $c>0$.
-/
@[category research solved, AMS 52]
theorem erdos_98.variants.upper_bound :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (h n : ℝ) < (n : ℝ) * Real.exp (c * Real.sqrt (Real.log (n : ℝ))) := by
  sorry

end Erdos98
