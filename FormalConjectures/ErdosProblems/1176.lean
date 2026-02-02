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
# Erdős Problem 1176

*Reference:* [erdosproblems.com/1176](https://www.erdosproblems.com/1176)
-/

open Cardinal

namespace Erdos1176

/--
Let $G$ be a graph with chromatic number $\aleph_1$. Is it true that there is a colouring of the
edges with $\aleph_1$ many colours such that, in any countable colouring of the vertices, there
exists a vertex colour containing all edge colours?

A problem of Erdős, Galvin, and Hajnal. The consistency of this was proved by Hajnal and Komjáth.
-/
@[category research open, AMS 3 5]
theorem erdos_1176 :
    answer(sorry) ↔ ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = aleph 1 →
      ∃ (EColor : Type) (_ : mk EColor = aleph 1) (c_edge : G.edgeSet → EColor),
        ∀ (VColor : Type) (_ : mk VColor ≤ aleph 0) (c_vert : V → VColor),
          ∃ (vc : VColor),
            ∀ (ec : EColor), ∃ (u v : V) (h : G.Adj u v),
              c_vert u = vc ∧ c_vert v = vc ∧ c_edge ⟨s(u, v), h⟩ = ec := by
  sorry

end Erdos1176
