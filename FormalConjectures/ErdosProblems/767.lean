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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 767

*References:*
- [erdosproblems.com/767](https://www.erdosproblems.com/767)
- [Er64c] Erdős, P., _Extremal problems in graph theory_. Theory of Graphs and its Applications
  (Proc. Sympos. Smolenice, 1963) (1964), 29-36.
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. Congr. Numer.
  (1975), 3-14.
- [Ji04] Jiang, Tao, _A note on a conjecture about cycles with many incident chords_. J. Graph
  Theory (2004), 180-182.
-/

@[expose] public section

open SimpleGraph

namespace Erdos767

/-- `G` contains a cycle with `k` chords incident to a vertex on the cycle. -/
def HasCycleWithIncidentChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

open scoped Classical in
/-- `g k n` is the maximal number of edges possible on a graph with `n` vertices which does not
contain a cycle with `k` chords incident to a vertex on the cycle. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n),
    ¬ HasCycleWithIncidentChords G k ∧ G.edgeFinset.card = m}

/--
Let $g_k(n)$ be the maximal number of edges possible on a graph with $n$ vertices which does not
contain a cycle with $k$ chords incident to a vertex on the cycle. Is it true that
$$g_k(n)=(k+1)n-(k+1)^2$$
for $n$ sufficiently large?

The answer is yes: the conjectured equality was proved for $n\geq 3k+3$ by Jiang [Ji04].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos767.lean#L1566"]
theorem erdos_767 : answer(True) ↔
    ∀ k ≥ 1, ∀ n ≥ 3 * k + 3, g k n = (k + 1) * n - (k + 1) ^ 2 := by
  sorry

/-- Czipszer proved that $g_k(n)\leq (k+1)n$. -/
@[category research solved, AMS 5]
theorem erdos_767.variants.czipszer (k n : ℕ) : g k n ≤ (k + 1) * n := by
  sorry

/-- Pósa proved that $g_1(n)=2n-4$ for $n\geq 4$. -/
@[category research solved, AMS 5]
theorem erdos_767.variants.posa (n : ℕ) (hn : 4 ≤ n) : g 1 n = 2 * n - 4 := by
  sorry

end Erdos767
