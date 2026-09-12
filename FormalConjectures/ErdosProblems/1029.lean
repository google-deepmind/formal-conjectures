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
# Erdős Problem 1029

*References:*
- [erdosproblems.com/1029](https://www.erdosproblems.com/1029)
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory.
  Quaestiones Math. (1993), 333-350.
- [ErSz35] Erdős, P. and Szekeres, G., A combinatorial problem in geometry. Compos. Math. (1935),
  463-470.
- [Sp75] Spencer, J., Ramsey's theorem - a new lower bound. J. Combin. Theory Ser. A (1975),
  108-115.
-/

open Filter

namespace Erdos1029

/--
If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the edges
of $K_n$ contains a monochromatic copy of $K_k$, then
$$\frac{R(k)}{k2^{k/2}}\to \infty.$$

In [Er93] Erdős offers $100 for a proof of this and $1000 for a disproof, but says 'this last offer
is to some extent phoney: I am sure that this is true (but I have been wrong before).'
-/
@[category research open, AMS 5]
theorem erdos_1029 :
    Tendsto (fun k : ℕ ↦ (SimpleGraph.diagonalRamsey k : ℝ) /
      ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))) atTop atTop := by
  sorry

-- TODO: Add variants of the problem.

end Erdos1029
