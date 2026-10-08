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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 925

*References:*
- [erdosproblems.com/925](https://www.erdosproblems.com/925)
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [AlRo05] Alon, Noga and Rödl, Vojtěch, _Sharp bounds for some multicolor Ramsey numbers_.
  Combinatorica (2005), 125--141.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos925

/-- `G` is not Ramsey for $K_3$: there is a $2$-colouring of the edges of `G` (a decomposition
`G = red ⊔ blue` into edge-disjoint graphs) with no monochromatic triangle. -/
def IsNotRamseyForTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ red blue : SimpleGraph V, Disjoint red blue ∧ red ⊔ blue = G ∧
    red.CliqueFree 3 ∧ blue.CliqueFree 3

/--
Is there a constant $\delta>0$ such that, for all large $n$, if $G$ is a graph on $n$ vertices
which is not Ramsey for $K_3$ (i.e. there exists a 2-colouring of the edges of $G$ with no
monochromatic triangle) then $G$ contains an independent set of size $\gg n^{1/3+\delta}$?

It is easy to show that there exists an independent set of size $\gg n^{1/3}$. In other words,
this question asks whether $R(3,3,m) \ll m^{3-c}$ for some $c>0$. This was disproved by Alon and
Rödl [AlRo05], who proved that
$$\frac{1}{(\log m)^{4+o(1)}}m^3 \ll R(3,3,m) \ll \frac{\log\log m}{(\log m)^2}m^3.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos925.lean#L706"]
theorem erdos_925 : answer(False) ↔
    ∃ δ > 0, ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      IsNotRamseyForTriangle G → c * (n : ℝ) ^ (1 / 3 + δ : ℝ) ≤ G.indepNum := by
  sorry

/-- It is easy to show that there exists an independent set of size $\gg n^{1/3}$. -/
@[category textbook, AMS 5]
theorem erdos_925.variants.cube_root :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      IsNotRamseyForTriangle G → c * (n : ℝ) ^ (1 / 3 : ℝ) ≤ G.indepNum := by
  sorry

end Erdos925
