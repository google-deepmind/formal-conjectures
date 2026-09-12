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
# Erdős Problem 1013

*References:*
- [erdosproblems.com/1013](https://www.erdosproblems.com/1013)
- [erdosproblems.com/920](https://www.erdosproblems.com/920)
- [erdosproblems.com/1104](https://www.erdosproblems.com/1104)
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [GrYa68] Graver, Jack E. and Yackel, James, Some graph theoretic results associated with Ramsey's
  theorem. J. Combinatorial Theory (1968), 125--175.
-/

open Asymptotics Filter Real SimpleGraph

open scoped Topology

namespace Erdos1013

/--
$h_3(k)$ is the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with
chromatic number $k$.

This is dual to the function $f(n)$ of [erdosproblems.com/1104](https://www.erdosproblems.com/1104):
$h_3(k)=n$ if and only if $n$ is minimal such that $f(n)=k$. See also
[erdosproblems.com/920](https://www.erdosproblems.com/920) for a generalisation to $K_r$-free graphs.
-/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞)}

/--
Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with
chromatic number $k$. Find an asymptotic for $h_3(k)$.
-/
@[category research open, AMS 5]
theorem erdos_1013.parts.i :
    (fun k ↦ (h3 k : ℝ)) ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with
chromatic number $k$. Prove
$$\lim_{k\to \infty}\frac{h_3(k+1)}{h_3(k)}=1.$$
-/
@[category research open, AMS 5]
theorem erdos_1013.parts.ii :
    Tendsto (fun k : ℕ ↦ (h3 (k + 1) : ℝ) / (h3 k : ℝ)) atTop (𝓝 1) := by
  sorry

/--
Graver and Yackel [GrYa68] proved
$$h_3(k)\gg \frac{\log k}{\log\log k}k^2.$$
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.graver_yackel :
    (fun k ↦ (h3 k : ℝ)) ≫ (fun k ↦ log k / log (log k) * (k : ℝ) ^ 2) := by
  sorry

/--
The bounds for $f(n)$ from [erdosproblems.com/1104](https://www.erdosproblems.com/1104) imply
$$\left(\frac{1}{2}-o(1)\right)k^2\log k\leq h_3(k) \leq (1+o(1))k^2\log k.$$
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.bounds :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ((1 : ℝ) / 2 - ε) * (k : ℝ) ^ 2 * log k ≤ (h3 k : ℝ) ∧
        (h3 k : ℝ) ≤ (1 + ε) * (k : ℝ) ^ 2 * log k := by
  sorry

end Erdos1013
