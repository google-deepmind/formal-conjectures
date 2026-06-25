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
# Erdős Problem 134

*Reference:* [erdosproblems.com/134](https://www.erdosproblems.com/134)
-/

namespace Erdos134

/--
Let $\epsilon,\delta>0$ and $n$ be sufficiently large in terms of $\epsilon$ and $\delta$.
Let $G$ be a triangle-free graph on $n$ vertices with maximum degree $<n^{1/2-\epsilon}$.
Can $G$ be made into a triangle-free graph with diameter $2$ by adding at most $\delta n^2$ edges?
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos134.lean"]
theorem erdos_134 : answer(True) ↔
    ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ),
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (∀ v : Fin n, (G.degree v : ℝ) < Real.rpow (n : ℝ) ((1 : ℝ) / 2 - ε)) →
      ∃ H : SimpleGraph (Fin n),
        G ≤ H ∧
        H.CliqueFree 3 ∧
        (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
        ((H.edgeFinset \ G.edgeFinset).card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  sorry

end Erdos134
