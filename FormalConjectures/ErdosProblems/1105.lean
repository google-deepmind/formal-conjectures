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
- [ESS75] Erdős, P. and Simonovits, M. and Sós, V. T., Anti-{R}amsey theorems. (1975), 633--643.
- [MoNe05] Montellano-Ballesteros, J. J. and Neumann-Lara, V., An anti-{R}amsey theorem on cycles.
  Graphs Combin. (2005), 343--354.
- [SiSo84] Simonovits, Miklós and Sós, Vera T., On restricted colourings of {$K_n$}. Combinatorica
  (1984), 101--110.
- [Yu21] L.-T. Yuan, The anti-Ramsey number for paths. arXiv:2102.00807 (2021).
-/

namespace Erdos1105

open SimpleGraph Asymptotics Filter

/--
The anti-Ramsey number $\mathrm{AR}(n,G)$ is the maximum possible number of colours in which the
edges of $K_n$ can be coloured without creating a rainbow copy of $G$ (i.e. one in which all edges
have different colours).

Let $C_k$ be the cycle on $k$ vertices. Is it true that
$\mathrm{AR}(n,C_k)=\left(\frac{k-2}{2}+\frac{1}{k-1}\right)n+O(1)$?

Montellano-Ballesteros and Neumann-Lara [MoNe05] gave an exact formula for $\mathrm{AR}(n,C_k)$,
which implies in particular that
$\mathrm{AR}(n,C_k)=\left(\frac{k-2}{2}+\frac{1}{k-1}\right)n+O(1).$
-/
@[category research solved, AMS 05]
theorem erdos_1105.parts.i : answer(True) ↔
    ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  sorry

/--
Let $P_k$ be the path on $k$ vertices and $\ell=\lfloor\frac{k-1}{2}\rfloor$. If $n\geq k\geq 5$
then is $\mathrm{AR}(n,P_k)$ equal to $\max\left(\binom{k-2}{2}+1,
\binom{\ell-1}{2}+(\ell-1)(n-\ell+1)+\epsilon\right)$where $\epsilon=1$ if $k$ is odd and
$\epsilon=2$ otherwise?

A proof of the formula for $\mathrm{AR}(n,P_k)$ for all $n\geq k\geq 5$ has been announced by
Yuan [Yu21].
-/
@[category research solved, AMS 05]
theorem erdos_1105.parts.ii : answer(True) ↔
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε) := by
  sorry

-- TODO: Add Erdős, Simonovits, and Sós variant.
-- TODO: Add Simonovits and Sós variant.

end Erdos1105
