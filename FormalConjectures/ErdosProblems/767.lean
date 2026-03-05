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
# Erdős Problem 767

*Reference:* [erdosproblems.com/767](https://www.erdosproblems.com/767)

Let $g_k(n)$ be the maximal number of edges possible on a graph with $n$ vertices
which does not contain a cycle with $k$ chords incident to a vertex on the cycle.

Czipszer proved that $g_k(n)$ exists for all $k$, and in fact $g_k(n) \leq (k+1)n$.
Pósa proved that $g_1(n) = 2n - 4$ for $n \geq 4$.
The conjectured equality was proved for $n \geq 3k + 3$ by Jiang [Ji04].

[Ji04] Jiang, T., _On the Turán number of cycles with $k$ chords_, 2004.
-/

open SimpleGraph

namespace Erdos767

/-- A graph $G$ contains a cycle with at least $k$ chords incident to a single vertex.
That is, there exists a simple cycle (given by an injective map $f : \operatorname{Fin} m \to V$
tracing consecutive adjacent vertices) and a vertex $f(i_0)$ on the cycle that
is adjacent to at least $k$ other cycle vertices which are not its two
cycle-neighbors. -/
def HasCycleWithKChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (hm : m ≥ 3) (f : Fin m → V),
    Function.Injective f ∧
    (∀ i : Fin m, G.Adj (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) ∧
    ∃ i₀ : Fin m,
      k ≤ Set.ncard {j : Fin m |
        j ≠ i₀ ∧
        j.val ≠ (i₀.val + 1) % m ∧
        j.val ≠ (i₀.val + m - 1) % m ∧
        G.Adj (f i₀) (f j)}

/-- $g_k(n)$: the maximum number of edges in a simple graph on $n$ vertices that
does not contain a cycle with $k$ chords incident to a vertex. -/
noncomputable def maxEdgesAvoidingCycleChords (k n : ℕ) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬HasCycleWithKChords G k ∧ G.edgeSet.ncard = e}

/--
**Erdős Problem 767** (proved by Jiang [Ji04]):

For all $k \geq 1$, $g_k(n) = (k+1)n - (k+1)^2$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_767 : answer(True) ↔
    ∀ (k : ℕ), k ≥ 1 → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      maxEdgesAvoidingCycleChords k n = (k + 1) * n - (k + 1) ^ 2 := by
  sorry

end Erdos767
