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
# Erdős Problem 737

*References:*
- [erdosproblems.com/737](https://www.erdosproblems.com/737)
- [EHS74] Erdős, P. and Hajnal, A. and Shelah, S., *On some general properties of chromatic
  numbers*. Topics in topology (Proc. Colloq., Keszthely, 1972) (1974), 243-255.
- [Th83] Thomassen, Carsten, *Cycles in graphs of uncountable chromatic number*. Combinatorica
  (1983), 133-134.
-/

@[expose] public section

namespace Erdos737

/--
`G` has chromatic number exactly $\aleph_1$: it has a proper colouring by the countable ordinals
(a set of cardinality $\aleph_1$) but no proper colouring by `ℕ`.
-/
def ChromaticNumberAlephOne {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ IsEmpty (G.Coloring ℕ)

/-- `G` contains a cycle of length `n` that contains the edge `e`. -/
def CycleThroughEdgeOfLength {V : Type*} (G : SimpleGraph V) (e : Sym2 V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n ∧ e ∈ c.edges

/-- The empty graph on `ℕ` is countably colourable, so it does not have chromatic number
$\aleph_1$. -/
@[category test, AMS 5]
theorem not_chromaticNumberAlephOne_bot : ¬ ChromaticNumberAlephOne (⊥ : SimpleGraph ℕ) := by
  intro h
  have : Nonempty ((⊥ : SimpleGraph ℕ).Coloring ℕ) :=
    ⟨SimpleGraph.Coloring.mk (fun _ => 0) (by simp)⟩
  exact (not_isEmpty_iff.mpr this) h.2

/--
Let $G$ be a graph with chromatic number $\aleph_1$. Must there exist an edge $e$ such that, for
all large $n$, $G$ contains a cycle of length $n$ containing $e$?

The answer is yes, proved by Thomassen [Th83]. Erdős, Hajnal, and Shelah [EHS74] proved that $G$
must contain all sufficiently large cycles (see Erdős Problem 594).
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos737.lean#L1266"]
theorem erdos_737 :
    ∀ (V : Type) (G : SimpleGraph V), ChromaticNumberAlephOne G →
      ∃ e ∈ G.edgeSet, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        CycleThroughEdgeOfLength G e n := by
  sorry

/--
The title and abstract of [Th83] state the result for graphs of uncountable chromatic number,
that is, graphs with no proper colouring by `ℕ`. This is stronger than `erdos_737`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos737.lean#L1181"]
theorem erdos_737.variants.uncountable :
    ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
      ∃ e ∈ G.edgeSet, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        CycleThroughEdgeOfLength G e n := by
  sorry

end Erdos737
