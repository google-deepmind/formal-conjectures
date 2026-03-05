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
# Erdős Problem 59

*Reference:* [erdosproblems.com/59](https://www.erdosproblems.com/59)

Is it true that for every graph $G$, the number of labeled $G$-free graphs on $n$ vertices
is at most $2^{(1+o(1)) \cdot \operatorname{ex}(n; G)}$? Disproved: the answer is no for
$G = C_6$ (Morris and Saxton [MoSa16]). Erdős, Frankl, and Rödl [EFR86] proved the
answer is yes when $G$ is not bipartite.
-/

open SimpleGraph

namespace Erdos59

/-- An injective graph homomorphism from $H$ to $G$; witnesses that $G$ contains a
subgraph isomorphic to $H$. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number $\operatorname{ex}(n; H)$: the maximum number of edges in a simple graph on
$n$ vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

/-- The number of labeled simple graphs on $n$ vertices that do not contain $H$ as a subgraph. -/
noncomputable def countGFreeGraphs {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  Nat.card {F : SimpleGraph (Fin n) // ¬ContainsSubgraph F H}

/--
Erdős Problem 59 [Er90, Er93, Er97c, Va99]:

Is it true that, for every graph $G$, the number of labeled graphs on $n$ vertices that
contain no copy of $G$ is at most $2^{(1+o(1)) \cdot \operatorname{ex}(n; G)}$?

That is, for every $\varepsilon > 0$, for all sufficiently large $n$:
$$\#\{\text{$G$-free graphs on $[n]$}\} \leq 2^{(1+\varepsilon) \cdot \operatorname{ex}(n; G)}$$

This was DISPROVED: the answer is no for $G = C_6$ (the 6-cycle).
Erdős, Frankl, and Rödl [EFR86] proved the answer is yes when $G$ is not bipartite.
Morris and Saxton [MoSa16] showed there are at least $2^{(1+c) \cdot \operatorname{ex}(n; C_6)}$
such graphs for infinitely many $n$, for some constant $c > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_59 : answer(False) ↔
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countGFreeGraphs H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (turanNumber H n : ℝ)) := by
  sorry

end Erdos59
