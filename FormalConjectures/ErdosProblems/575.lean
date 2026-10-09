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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 575

*References:*
- [erdosproblems.com/575](https://www.erdosproblems.com/575)
- [ErSi82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
  Combinatorica **2** (1982), 275-288.
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science* (2026).
- [PALOMAR-2026-10-06-000004](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-06-000004&version=1)
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos575

/-- A finite graph, bundled with its vertex count, so that a family may mix orders. -/
structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

/-- A host graph is `family`-free when it contains no member of `family` as a subgraph. -/
def FamilyFree (family : Finset FiniteGraph) {n : ℕ} (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

open scoped Classical in
/-- $\mathrm{ex}(n;\mathcal{F})$, the greatest number of edges of a graph on `n` vertices
containing no member of `family`. -/
noncomputable def familyExtremal (family : Finset FiniteGraph) (n : ℕ) : ℕ :=
  (Finset.univ.filter (FamilyFree family)).sup
    fun host : SimpleGraph (Fin n) => host.edgeFinset.card

/-- No member of the family is acyclic. -/
def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

/-- The family contains at least one bipartite member. -/
def ContainsBipartiteMember (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, forbidden.graph.IsBipartite

/-- Eventual constant-factor control of the family extremal number by a single graph. -/
def ControlsFamily (family : Finset FiniteGraph) (forbidden : FiniteGraph) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (extremalNumber n forbidden.graph : ℝ) ≤ C * (familyExtremal family n : ℝ)

/-- The family is *bipartite-compact*: some bipartite member already controls the family extremal
number. -/
def IsBipartiteCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, forbidden.graph.IsBipartite ∧ ControlsFamily family forbidden

open scoped Classical in
/-- Every `family`-free graph on `n` vertices has at most $\binom{n}{2}$ edges. -/
@[category test, AMS 5]
theorem familyExtremal_le_choose_two (family : Finset FiniteGraph) (n : ℕ) :
    familyExtremal family n ≤ n.choose 2 := by
  unfold familyExtremal
  refine Finset.sup_le fun host _ => ?_
  simpa using host.card_edgeFinset_le_card_choose_two

/--
If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum
number of edges a graph on $n$ vertices can have without containing any subgraphs from
$\mathcal{F}$. Is it true that, if $\mathcal{F}$ contains a bipartite graph, then there exists a
bipartite $G\in\mathcal{F}$ such that
$$\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})?$$

As noted by Yuval Wigderson on [erdosproblems.com/575](https://www.erdosproblems.com/575), the
unrestricted statement without excluding forests has the trivial counterexample
$\mathcal{F}=\{K_{1,2}, 2K_2\}$ (see `erdos_575.variants.unrestricted`), so the intended question
requires every member of $\mathcal{F}$ to contain a cycle (`IsCyclicFamily`). Even with forests
excluded, the answer is no: OpenAI [OpenAI26] give a finite nonempty family of connected bipartite
graphs, none of them acyclic, for which no single member controls the family extremal number
(see `erdos_575.variants.counterexample` and Problem 180).
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/linrock/math-proofs/blob/b135fd8f6e5ee25129c4855e06c93739dd80651d/erdos-575/Proofs/Erdos575.lean#L189"]
theorem erdos_575 : answer(False) ↔
    ∀ family : Finset FiniteGraph,
      family.Nonempty → IsCyclicFamily family →
        ContainsBipartiteMember family → IsBipartiteCompactFamily family := by
  sorry

/--
The literal catalog statement without `IsCyclicFamily family` is also false, already for the
forest family $\mathcal{F}=\{K_{1,2}, 2K_2\}$, where $\mathrm{ex}(n;\mathcal{F})=1$ for $n\ge 4$
while $\mathrm{ex}(n;K_{1,2})=\lfloor n/2\rfloor$ and $\mathrm{ex}(n;2K_2)=n-1$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/linrock/math-proofs/blob/b135fd8f6e5ee25129c4855e06c93739dd80651d/erdos-575/Proofs/Erdos575.lean#L197"]
theorem erdos_575.variants.unrestricted : answer(False) ↔
    ∀ family : Finset FiniteGraph,
      family.Nonempty → ContainsBipartiteMember family → IsBipartiteCompactFamily family := by
  sorry

/--
The non-forest counterexample: a nonempty cyclic family of connected bipartite graphs that is not
bipartite-compact.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/linrock/math-proofs/blob/b135fd8f6e5ee25129c4855e06c93739dd80651d/erdos-575/Proofs/Erdos575.lean#L111"]
theorem erdos_575.variants.counterexample :
    ∃ family : Finset FiniteGraph,
      family.Nonempty ∧
      IsCyclicFamily family ∧
      ContainsBipartiteMember family ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      ¬ IsBipartiteCompactFamily family := by
  sorry

end Erdos575
