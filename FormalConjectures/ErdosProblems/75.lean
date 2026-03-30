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
# Erdős Problem #75

Is there a graph of chromatic number \(\aleph_1\) with \(\aleph_1\) vertices such that for all \(\epsilon > 0\), if \(n\) is sufficiently large and \(H\) is a subgraph on \(n\) vertices, then \(H\) contains an independent set of size \(> n^{1-\epsilon}\)?

**Conjectured by** Erdős, Hajnal, and Szemerédi [[EHS82]].
**Reference:** [Erdős Problems #75](https://www.erdosproblems.com/75)
-/

namespace Erdos075

/-- English version: "Is there a graph of chromatic number \(\aleph_1\) with \(\aleph_1\) vertices such that for all \(\epsilon>0\) if \(n\) is sufficiently large and \(H\) is a subgraph on \(n\) vertices then \(H\) contains an independent set of size \(>n^{1-\epsilon}\)?" -/
@[category research open, AMS 05]
theorem erdos_problem_75 :
    answer(sorry) ↔
      ∃ (G : Type) (_ : Graph G),
        G.chromaticNumber = ℵ₁ ∧ G.vertexSet.card = ℵ₁ ∧
        ∀ (ε : ℝ) (hε : 0 < ε),
          ∃ (N : ℕ),
            ∀ (H : G.Subgraph) (n : ℕ) (hn : n ≥ N) (hcard : H.verts.card = n),
              ∃ (I : Set G), I ⊆ H.verts ∧ I.IsIndependent ∧ I.card > (n : ℝ) ^ (1 - ε) := by
  sorry

end Erdos075
