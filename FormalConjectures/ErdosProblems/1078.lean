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
# Erdős Problem 1078

*Reference:* [erdosproblems.com/1078](https://www.erdosproblems.com/1078)

If $G$ is an $r$-partite graph with $n$ vertices in each part and minimum degree at least
$(r - 3/2 - \varepsilon) \cdot n$, must $G$ contain a transversal copy of $K_r$?

[BES75b] Bollobás, B., Erdős, P., and Szemerédi, E., proved that the threshold
$r - 3/2$ is best possible.

[Ha01] Haxell, P., proved the conjecture.

[HaSz06] Haxell, P. and Szabó, T., proved the sharp threshold of
$(r-1)n - \lceil sn/(2s-1) \rceil$ where $s = \lfloor r/2 \rfloor$.
-/

open SimpleGraph

namespace Erdos1078

/-- An $r$-partite graph on vertex set `Fin r × Fin n`: no edges within any part. -/
def IsMultipartite {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∀ (i : Fin r) (a b : Fin n), ¬G.Adj (i, a) (i, b)

/-- A transversal clique in an $r$-partite graph: a choice of one vertex from each
part such that all chosen vertices are pairwise adjacent. This corresponds
to a copy of $K_r$ in an $r$-partite graph. -/
def HasTransversalClique {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∃ f : Fin r → Fin n, ∀ i j : Fin r, i ≠ j → G.Adj (i, f i) (j, f j)

/--
Erdős Problem 1078 [BES75b, Ha01]:

For all $r \geq 2$, for every $\varepsilon > 0$, there exists $n_0$ such that for all
$n \geq n_0$, every $r$-partite graph $G$ with $n$ vertices in each part and minimum degree
$\geq (r - 3/2 - \varepsilon) \cdot n$ contains a transversal clique $K_r$.

Bollobás, Erdős, and Szemerédi [BES75b] proved that $r - 3/2$ is best possible.
Proved by Haxell [Ha01]. The sharp threshold of $(r-1)n - \lceil sn/(2s-1) \rceil$
where $s = \lfloor r/2 \rfloor$ was proved by Haxell and Szabó [HaSz06].
-/
@[category research solved, AMS 5]
theorem erdos_1078 (r : ℕ) (hr : r ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ (G : SimpleGraph (Fin r × Fin n)) [DecidableRel G.Adj],
      IsMultipartite G →
      (∀ v : Fin r × Fin n, (G.degree v : ℝ) ≥ ((r : ℝ) - 3 / 2 - ε) * (n : ℝ)) →
      HasTransversalClique G := by
  sorry

end Erdos1078
