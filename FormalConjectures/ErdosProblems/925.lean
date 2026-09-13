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
# Erdős Problem 925

*References:*
- [erdosproblems.com/925](https://www.erdosproblems.com/925)
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [AlRo05] Alon, Noga and Rödl, Vojtěch, *Sharp bounds for some multicolor Ramsey numbers*.
  Combinatorica (2005), 125--141.
-/

open Filter SimpleGraph

namespace Erdos925

/--
A graph `G` is *Ramsey for* $K_3$ if every $2$-colouring of the edges of `G` contains a
monochromatic triangle.
-/
def IsRamseyForK3 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (c : Fin 2 → SimpleGraph V), G.IsEdgeColouring c → ∃ i, ¬ (c i).CliqueFree 3

/--
Is there a constant $\delta>0$ such that, for all large $n$, if $G$ is a graph on $n$ vertices
which is not Ramsey for $K_3$ (i.e. there exists a 2-colouring of the edges of $G$ with no
monochromatic triangle) then $G$ contains an independent set of size $\gg n^{1/3+\delta}$?

It is easy to show that there exists an independent set of size $\gg n^{1/3}$.

In other words, this question asks whether $R(3,3,m) \ll m^{3-c}$ for some $c>0$. This was
disproved by Alon and Rödl [AlRo05], who proved that
$$\frac{1}{(\log m)^{4+o(1)}}m^3 \ll R(3,3,m) \ll \frac{\log\log m}{(\log m)^2}m^3.$$
As reported in [AlRo05] Sudakov has observed that the $\log\log m$ in the upper bound can be
removed.

See also [553](https://www.erdosproblems.com/553).
-/
@[category research solved, AMS 5]
theorem erdos_925 : answer(False) ↔
    ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      ¬ IsRamseyForK3 G → C * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ (G.indepNum : ℝ) := by
  sorry

/--
It is easy to show that there exists an independent set of size $\gg n^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_925.variants.cube_root :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      ¬ IsRamseyForK3 G → C * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (G.indepNum : ℝ) := by
  sorry

end Erdos925
