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
# Reed's omega, delta, and chi conjecture

*References*:
- [B. Reed,  ω Δ and χ, J. Graph Theory 27 (1998) 177-212.](https://onlinelibrary.wiley.com/doi/10.1002/(SICI)1097-0118(199804)27:4%3C177::AID-JGT1%3E3.0.CO;2-K) 
-
[openproblemgarden(http://www.openproblemgarden.org/op/reeds_omega_delta_and_chi_conjecture)
- [mathoverflow/37923](https://mathoverflow.net/questions/37923) asked by user [Andrew D. King](https://mathoverflow.net/users/4580/andrew-d-king)
-/

namespace ReedOmegaDeltaChi

open Classical

noncomputable
def maxDegree {V : Type} (G : SimpleGraph V) : ℕ∞ :=
  if h : ∀ v, Finite (G.neighborSet v) then
    have : ∀ v, Fintype (G.neighborSet v) :=
      fun v => @Fintype.ofFinite _ (h v)
    ⨆ v, G.degree v
  else
    ⊤

/--
For a nonempty graph, `G.cliqueNum` is 0 iff the clique size is unbounded. For the purposes of
stating the conjecture, we actually want the max clique size to be `∞` in this case.
-/
noncomputable
def maxCliqueSize {V : Type} (G : SimpleGraph V) : ℕ∞ :=
  if Nonempty V ∧ G.cliqueNum = 0 then ⊤ else G.cliqueNum

/--
For a graph $G$, we define $\Delta(G)$ to be the maximum degree, $\omega(G)$ to be the size of the
largest clique subgraph, and $\chi(G)$ to be the chromatic number. Reed's omega, delta, and chi
conjecture states that $$\chi(G) \leq \lceil \frac{1}{2}(\omega(G) + \Delta(G) + 1) \rceil.$$
-/
@[category research open, AMS 5]
theorem reed_omega_delta_chi_conjecture :
  ∀ {V : Type} (G : SimpleGraph V),
    let χ := G.chromaticNumber
    let ω := maxCliqueSize G
    let Δ := maxDegree G
  /- (d+1)/2 = ⌈d/2⌉ -/
  χ ≤ (ω + Δ + 1).map (fun d => (d + 1) / 2) := by
    sorry

/--
The simplest open case is when $\Delta(G) = 6$ and $\omega(G) = 2$.
-/
@[category research open, AMS 5]
theorem reed_conjecture_Δ_6_ω_2 :
  ∀ {V : Type} (G : SimpleGraph V), maxDegree G = 6 ∧ G.cliqueNum = 2 → G.chromaticNumber ≤ 5 := by
    sorry

end ReedOmegaDeltaChi
