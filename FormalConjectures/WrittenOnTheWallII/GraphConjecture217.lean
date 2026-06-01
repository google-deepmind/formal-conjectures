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
# Written on the Wall II - Conjecture 217

Per the WOWII definitions popup linked from this conjecture:

- $L(G)$ is the **maximum number of leaves of a spanning tree** of $G$
  — i.e. `Ls G` in our invariant library.
- $\chi_{\mathrm{residue}=2}(G)$ is the **characteristic function** for the
  predicate $\mathrm{residue}\, G = 2$, i.e. $1$ when $\mathrm{residue}\, G = 2$
  and $0$ otherwise. It is not a connected-component count of any 2-core.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **characteristic function** for the predicate $\mathrm{residue}\, G = 2$:
returns $1$ when $G.\mathrm{residue} = 2$ and $0$ otherwise. This is the WOWII
$\chi_{\mathrm{residue}=2}(G)$ indicator appearing in Conjecture 217. -/
noncomputable def residueEqTwoIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

/--
WOWII [Conjecture 217](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj217):

If $G$ is a finite simple connected graph on $n > 1$ vertices and
$L_s(G) \le 4 \cdot \chi_{\mathrm{residue}=2}(G) + 2$,
then $G$ has a Hamiltonian path. Here $L_s(G)$ is the maximum number of
leaves over all spanning trees and $\chi_{\mathrm{residue}=2}(G)$ is the indicator
of $\mathrm{residue}(G) = 2$.
-/
@[category research open, AMS 5]
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- `residueEqTwoIndicator` is always $0$ or $1$. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    residueEqTwoIndicator G ≤ 1 := by
  unfold residueEqTwoIndicator; split <;> simp

/-- `residueEqTwoIndicator` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    0 ≤ residueEqTwoIndicator G := Nat.zero_le _

-- The `Ls G` invariant is nonneg by construction (sSup of nonneg leaf counts);
-- proving it requires the sSup-nonempty / above-bound machinery. We omit a
-- sanity check here to avoid pulling in that infrastructure for a single test.

end WrittenOnTheWallII.GraphConjecture217
