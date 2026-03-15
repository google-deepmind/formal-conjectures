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
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Erdős Problem 575

Erdős and Simonovits asked whether, for every finite family of graphs containing a bipartite
member, some bipartite member has Turán number within a constant factor of the family Turán number.

*Reference:* [erdosproblems.com/575](https://www.erdosproblems.com/575)

[ErSi82] Erdős, P. and Simonovits, M., _Compactness results in extremal graph theory_,
Combinatorica **2** (1982), 275-288.
-/

open SimpleGraph

namespace Erdos575

/-- An injective graph homomorphism from $H$ to $G$: $G$ contains a copy of $H$ as a
subgraph. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number $\operatorname{ex}(n; H)$: the maximum number of edges in a simple graph on
$n$ vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

/-- The Turán number for a family $\operatorname{ex}(n; \mathcal{F})$: the maximum number of edges
in a simple graph on $n$ vertices that contains no copy of any member of the family $\mathcal{F}$
as a subgraph. -/
noncomputable def turanNumberFamily
    {ι : Type*} [Fintype ι]
    {k : ι → ℕ} (H : (i : ι) → SimpleGraph (Fin (k i))) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ (∀ i : ι, ¬ContainsSubgraph F (H i)) ∧ F.edgeFinset.card = m}

/--
Erdős Conjecture (Problem 575) [ErSi82]:

If $\mathcal{F}$ is a finite set of finite graphs containing at least one bipartite graph, then
there exists a bipartite $G \in \mathcal{F}$ such that
$\operatorname{ex}(n; G) \leq C \cdot \operatorname{ex}(n; \mathcal{F})$ for some constant $C$
depending on $\mathcal{F}$ and all $n \geq 1$.

See also Problem 180.
-/
@[category research open, AMS 5]
theorem erdos_575 : answer(sorry) ↔
    ∀ (ι : Type) [Fintype ι] [Nonempty ι]
      (k : ι → ℕ) (H : (i : ι) → SimpleGraph (Fin (k i))),
    (∃ i : ι, IsBipartite (H i)) →
    ∃ i : ι,
    IsBipartite (H i) ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (turanNumber (H i) n : ℝ) ≤ C * (turanNumberFamily H n : ℝ) := by
  sorry

end Erdos575
