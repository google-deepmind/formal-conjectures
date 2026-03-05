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
# Erdős Problem 618

*Reference:* [erdosproblems.com/618](https://www.erdosproblems.com/618)

A problem of Erdős, Gyárfás, and Ruszinkó [EGR98]. Simonovits showed that there exist
graphs $G$ with maximum degree $\gg n^{1/2}$ and $h_2(G) \gg n^2$. Proved in the
affirmative by Alon.
-/

open SimpleGraph

namespace Erdos618

/-- `triangleFreeDiam2Completion G` is the minimum number of edges that must be added
to a triangle-free graph `G` on `Fin n` so that the resulting supergraph has
diameter at most $2$ and remains triangle-free. -/
noncomputable def triangleFreeDiam2Completion {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n), G ≤ H ∧
    H.CliqueFree 3 ∧
    H.Connected ∧
    H.diam ≤ 2 ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

/--
**Erdős Problem 618** [EGR98]:

For a triangle-free graph $G$, let $h_2(G)$ be the smallest number of edges that need
to be added to $G$ so that it has diameter $2$ and is still triangle-free. If $G$ has
maximum degree $o(n^{1/2})$ then $h_2(G) = o(n^2)$.

Formulated as: for every $\varepsilon > 0$, there exist $\delta > 0$ and $N_0$ such that
for all $n \geq N_0$, for every triangle-free graph $G$ on $n$ vertices with every vertex
having degree at most $\delta \cdot n^{1/2}$, we have $h_2(G) \leq \varepsilon \cdot n^2$.

Proved by Alon.
-/
@[category research solved, AMS 5]
theorem erdos_618 :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (∀ v : Fin n, (G.degree v : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / 2)) →
      (triangleFreeDiam2Completion G : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos618
