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
# Erdős Problem 1105

*References:*
- [erdosproblems.com/1105](https://www.erdosproblems.com/1105)
- P. Erdős, M. Simonovits, V. T. Sós, "Anti-Ramsey theorems," Colloq. Math. Soc. János Bolyai
  10 (1975), 633–643.
- M. Simonovits, V. T. Sós, "On restricted colourings of $K_n$," Combinatorica 4 (1984), 101–110.
- L. Yuan, "Anti-Ramsey number of paths," Discrete Math. 344 (2021), 112412.
-/

namespace Erdos1105

open SimpleGraph Asymptotics Filter

/--
Is $\mathrm{AR}(n, C_k) = \left(\frac{k-2}{2} + \frac{1}{k-1}\right)n + O(1)$?
-/
@[category research open, AMS 05]
theorem erdos_1105_cycles (k : ℕ) (hk : 3 ≤ k) :
    answer(sorry) ↔ ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  sorry

/--
For $n \geq k \geq 5$, let $\ell = \lfloor(k-1)/2\rfloor$ and $\epsilon = 1$ if $k$ odd, else $2$.
Is $\mathrm{AR}(n, P_k) = \max\left(\binom{k-2}{2}+1,\; \binom{\ell-1}{2}+(\ell-1)(n-\ell+1)+\epsilon\right)$?
-/
@[category research open, AMS 05]
theorem erdos_1105_paths (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    answer(sorry) ↔ antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  sorry

end Erdos1105
