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
# Erdős Problem 1022

*Reference:* [erdosproblems.com/1022](https://www.erdosproblems.com/1022)

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.

[Lo68] Lovász, L., _On covering of graphs_. Theory of Graphs (Proc. Colloq., Tihany, 1966)
(1968), 231-236.

[Wo13b] Wood, D.R., _Hypergraph colouring and degeneracy_. arXiv:1310.2972 (2013).
-/

open Finset Filter

namespace Erdos1022

/-- A finite set family has **property B** (is 2-colorable) if there exists
    a 2-coloring of the ground set such that no edge is monochromatic:
    every edge contains elements of both colors. -/
def HasPropertyB {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∃ f : Fin n → Bool, ∀ e ∈ F, (∃ v ∈ e, f v = true) ∧ (∃ v ∈ e, f v = false)

/--
**Erdős Problem 1022** [Er71, p.105]:

There does NOT exist a function $c : \mathbb{N} \to \mathbb{R}$ with
$c(t) \to \infty$ as $t \to \infty$ such that the following holds: for every
$t$ and every finite hypergraph $\mathcal{F}$ on $n$ vertices, if all edges
have size $\geq t$ and for every vertex set $X$ the number of edges contained
in $X$ is $< c(t) \cdot |X|$, then $\mathcal{F}$ has property B.

Disproved by Wood [Wo13b].
-/
@[category research solved, AMS 5]
theorem erdos_1022 : answer(False) ↔
    ∃ (c : ℕ → ℝ), Tendsto c atTop atTop ∧
      ∀ (t : ℕ) (n : ℕ) (F : Finset (Finset (Fin n))),
        (∀ e ∈ F, t ≤ e.card) →
        (∀ X : Finset (Fin n),
          ((F.filter (fun e => e ⊆ X)).card : ℝ) ≤ c t * (X.card : ℝ)) →
        HasPropertyB F := by sorry

end Erdos1022
