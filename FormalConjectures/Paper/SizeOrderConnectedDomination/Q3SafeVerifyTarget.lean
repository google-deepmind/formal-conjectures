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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture2

/-! SafeVerify target for Mukwembi's Theorem 2.1 (false).

The statement claims: for every connected triangle-free graph G,
  m ≤ (n - γ_c)² / 4 + n - 1.

Q₃ is a counterexample (m = 12 > 11). -/

open SimpleGraph

theorem mukwembi_size_bound
    (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hTF : G.CliqueFree 3) :
    (G.edgeFinset.card : ℝ) ≤
      ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
      + (Fintype.card α : ℝ) - 1 := by
  sorry
