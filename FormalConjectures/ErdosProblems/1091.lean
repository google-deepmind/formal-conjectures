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
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1091

Let G be a K₄-free graph with chromatic number 4. Must G contain an odd cycle with at least
two diagonals?

More generally, is there some f(r) → ∞ such that every graph with chromatic number 4,
in which every subgraph on ≤r vertices has chromatic number ≤3, contains an odd cycle with
at least f(r) diagonals?

*Reference:* [erdosproblems.com/1091](https://www.erdosproblems.com/1091)
-/

namespace Erdos1091

open SimpleGraph Filter

variable {V : Type*}

/--
A diagonal of a cycle is an edge connecting two non-adjacent vertices in the cycle.
Given a cycle `c` in a graph `G`, this counts the number of diagonals.
-/
def cycleNumberOfDiagonals (G : SimpleGraph V) {v : V} (c : G.Walk v v)
    (hcycle : c.IsCycle) : ℕ :=
  sorry

/--
An odd cycle in graph `G` has at least `k` diagonals.
-/
def hasOddCycleWithDiagonals (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v) (hcycle : c.IsCycle),
    Odd c.length ∧ cycleNumberOfDiagonals G c hcycle ≥ k

/--
Every subgraph of `G` on at most `r` vertices has chromatic number at most 3.
-/
def locallyThreeColorable (G : SimpleGraph V) [Fintype V] (r : ℕ) : Prop :=
  ∀ (S : Finset V), S.card ≤ r → (G.induce (↑S : Set V)).chromaticNumber ≤ 3

/--
**Erdős problem 1091 (first part)**

Let G be a K₄-free graph with chromatic number 4. Then G contains an odd cycle with
at least two diagonals.
-/
@[category research open, AMS 5]
theorem erdos_1091_part1 :
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree 4 → G.chromaticNumber = 4 →
      hasOddCycleWithDiagonals G 2 := by
  sorry

/--
**Erdős problem 1091 (general form)**

There exists a function f : ℕ → ℕ such that f(r) → ∞ as r → ∞, and every graph with
chromatic number 4, in which every subgraph on ≤r vertices has chromatic number ≤3,
contains an odd cycle with at least f(r) diagonals.
-/
@[category research open, AMS 5]
theorem erdos_1091_general :
    (∃ (f : ℕ → ℕ), Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (V : Type*) [Fintype V] (G : SimpleGraph V),
        G.chromaticNumber = 4 → locallyThreeColorable G r →
        hasOddCycleWithDiagonals G (f r)) ↔ answer(sorry) := by
  sorry

end Erdos1091
