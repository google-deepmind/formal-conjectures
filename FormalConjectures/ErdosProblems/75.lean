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
# Erdős Problem 75

Is there a graph of chromatic number \(\aleph_1\) with \(\aleph_1\) vertices such that for all
\(\epsilon > 0\), if \(n\) is sufficiently large and \(H\) is a subgraph on \(n\) vertices,
then \(H\) contains an independent set of size \(> n^{1-\epsilon}\)?

**Reference:** https://www.erdosproblems.com/75
-/
namespace Erdos075
open Cardinal

@[category research open, AMS 05]
theorem erdos_problem_75 :
    ∃ (V : Type) (G : SimpleGraph V),
      Cardinal.lift.{1} (G.chromaticNumber : Cardinal) = Cardinal.aleph 1 ∧
      Cardinal.mk V = Cardinal.aleph 1 ∧
      ∀ (ε : ℝ), 0 < ε →
        ∃ (N : ℕ),
          ∀ (n : ℕ) (H : G.Subgraph),
            n ≥ N →
            H.verts.ncard = n →
            ∃ (I : Finset V),
              (I : Set V) ⊆ H.verts ∧
              G.IsIndepSet (I : Set V) ∧
              (I.card : ℝ) > (n : ℝ) ^ (1 - ε) := by
  sorry

end Erdos075
