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
# Erdős Problem 752

*References:*
- [erdosproblems.com/752](https://www.erdosproblems.com/752)
- [Er92b] Erdős, Paul, _Some of my favourite problems in various branches of combinatorics_.
  Matematiche (Catania) (1992), 231-240.
- [Er93] Erdős, Paul, _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333-350.
- [Er94b] Erdős, Paul, _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261-269.
- [SuVe08] Sudakov, Benny and Verstraëte, Jacques, _Cycle lengths in sparse graphs_.
  Combinatorica (2008), 357--372.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos752

/-- The set of cycle lengths of `G`: the lengths of the simple cycles in `G`. -/
def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {l | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = l}

/--
Let $G$ be a graph with minimum degree $k$ and girth $>2s$ (i.e. $G$ contains no cycles of length
$\leq 2s$). Must there be $\gg k^s$ many distinct cycle lengths in $G$?

A question of Erdős, Faudree, and Schelp, who proved it when $s=2$. The answer is yes, proved by
Sudakov and Verstraëte [SuVe08], who in fact proved that under the assumption of average degree
$k$ and girth $>2s$ there are at least $\gg k^s$ many consecutive even integers which are cycle
lengths in $G$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos752.lean#L207"]
theorem erdos_752 : answer(True) ↔
    ∀ s : ℕ, 1 ≤ s → ∃ c > 0, ∀ᶠ k : ℕ in atTop,
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
        k ≤ G.minDegree → (2 * s : ℕ∞) < G.egirth →
          c * (k : ℝ) ^ s ≤ (cycleLengths G).ncard := by
  sorry

/--
Sudakov and Verstraëte [SuVe08] proved that under the assumption of average degree $k$ and girth
$>2s$ there are at least $\gg k^s$ many consecutive even integers which are cycle lengths in $G$.
-/
@[category research solved, AMS 5]
theorem erdos_752.variants.sudakov_verstraete :
    ∀ s : ℕ, 1 ≤ s → ∃ c > 0, ∀ᶠ k : ℕ in atTop,
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (k : ℚ) ≤ G.averageDegree → (2 * s : ℕ∞) < G.egirth →
          ∃ a m : ℕ, c * (k : ℝ) ^ s ≤ m ∧ ∀ i < m, 2 * (a + i) ∈ cycleLengths G := by
  sorry

end Erdos752
