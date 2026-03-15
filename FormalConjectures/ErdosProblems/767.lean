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

Erdős conjectured that $g_k(n) = (k+1)n - (k+1)^2$ for sufficiently large $n$, noting
that the lower bound $g_k(n) \geq (k+1)n - (k+1)^2$ is "easy to see."
Czipszer proved that $g_k(n)$ exists for all $k$, and in fact $g_k(n) \leq (k+1)n$.
Pósa proved that $g_1(n) = 2n - 4$ for $n \geq 4$.
Erdős verified the conjecture for $k = 2$ and $k = 3$ when $n \geq 2k + 2$.
The conjectured equality was proved for $n \geq 3k + 3$ by Jiang [Ji04].

In [Er69b], Erdős mentions that Lewin disproved the conjecture for general $k$ (oral
communication), though it is unclear whether this applied only to small $n$ or was incorrect,
given Jiang's later proof.

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
  Theory (1969), 27-35.
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

/--
**Czipszer's upper bound:**

For all $k$, $g_k(n) \leq (k+1)n$.
-/
@[category research solved, AMS 5]
theorem erdos_767_czipszer_upper_bound :
    ∀ (k n : ℕ), maxEdgesAvoidingCycleChords k n ≤ (k + 1) * n := by
  sorry

/--
**Pósa's exact result:**

$g_1(n) = 2n - 4$ for $n \geq 4$.
-/
@[category research solved, AMS 5]
theorem erdos_767_posa :
    ∀ (n : ℕ), n ≥ 4 → maxEdgesAvoidingCycleChords 1 n = 2 * n - 4 := by
  sorry

end Erdos767
