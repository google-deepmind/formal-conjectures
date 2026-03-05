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
# Erdős Problem 619

*Reference:* [erdosproblems.com/619](https://www.erdosproblems.com/619)

For a triangle-free graph $G$ let $h_r(G)$ be the smallest number of edges that
need to be added to $G$ so that it has diameter $r$ (while preserving the property
of being triangle-free).

[EGR98] Erdős, P., Gyárfás, A. and Ruszinkó, M., *How to decrease the diameter of
triangle-free graphs*, Combinatorica **18** (1998), 493–501.
-/

open SimpleGraph

namespace Erdos619

/-- `triangleFreeDiamCompletion r G` is the minimum number of edges that must be added
to a triangle-free graph `G` on `Fin n` so that the resulting supergraph has
diameter at most $r$ and remains triangle-free. Returns $0$ if no such completion
exists (the set is empty and `sInf` defaults to $0$). -/
noncomputable def triangleFreeDiamCompletion {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n), G ≤ H ∧
    H.CliqueFree 3 ∧
    H.Connected ∧
    H.diam ≤ r ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

/--
**Erdős Problem 619** [EGR98]:

Is it true that there exists a constant $c > 0$ such that for every connected
triangle-free graph $G$ on $n$ vertices, $h_4(G) < (1 - c) \cdot n$?

A problem of Erdős, Gyárfás, and Ruszinkó [EGR98] who proved that $h_3(G) \leq n$
and $h_5(G) \leq (n-1)/2$ and there exist connected graphs $G$ on $n$ vertices with
$h_3(G) \geq n - c$ for some constant $c > 0$.
-/
@[category research open, AMS 5]
theorem erdos_619 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      G.Connected →
      (triangleFreeDiamCompletion 4 G : ℝ) < (1 - c) * (n : ℝ) := by
  sorry

end Erdos619
