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
# Erdős Problem 797

*References:*
- [erdosproblems.com/797](https://www.erdosproblems.com/797)
- [AlBe76] Albertson, Michael O. and Berman, David M., _The acyclic chromatic number_. (1976),
  51-69.
- [AMR91] Alon, Noga and McDiarmid, Colin and Reed, Bruce, _Acyclic coloring of graphs_. Random
  Structures Algorithms (1991), 277-288.
-/

@[expose] public section

open Filter Real

namespace Erdos797

/-- A colouring `c` of the vertices of `G` is *acyclic* if there is no edge between vertices of
the same colour and no cycle containing only two colours. -/
def IsAcyclicColoring {V C : Type*} (G : SimpleGraph V) (c : V → C) : Prop :=
  (∀ u v, G.Adj u v → c u ≠ c v) ∧
    ∀ (v : V) (w : G.Walk v v), w.IsCycle →
      ¬ ∃ a b : C, ∀ u ∈ w.support, c u = a ∨ c u = b

open scoped Classical in
/-- `f d` is the maximal acyclic chromatic number of any graph with maximum degree `d`: the least
number of colours with which the vertices of any graph with maximum degree at most `d` can be
acyclically coloured. -/
noncomputable def f (d : ℕ) : ℕ :=
  sInf {k | ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.maxDegree ≤ d →
    ∃ c : Fin n → Fin k, IsAcyclicColoring G c}

/--
Let $f(d)$ be the maximal acyclic chromatic number of any graph with maximum degree $d$ - that
is, the vertices of any graph with maximum degree $d$ can be coloured with $f(d)$ colours such
that there is no edge between vertices of the same colour and no cycle containing only two
colours.

Estimate $f(d)$.

Resolved by Alon, McDiarmid, and Reed [AMR91] who showed
$$\frac{d^{4/3}}{(\log d)^{1/3}}\ll f(d) \ll d^{4/3}.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos797.lean#L3990"]
theorem erdos_797.parts.i : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop,
    c * (d : ℝ) ^ (4 / 3 : ℝ) / (log d) ^ (1 / 3 : ℝ) ≤ f d ∧
      (f d : ℝ) ≤ C * (d : ℝ) ^ (4 / 3 : ℝ) := by
  sorry

/--
Is it true that $f(d)=o(d^2)$?

The answer is yes: Alon, McDiarmid, and Reed [AMR91] showed $f(d)\ll d^{4/3}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos797.lean#L3990"]
theorem erdos_797.parts.ii : answer(True) ↔
    (fun d : ℕ ↦ (f d : ℝ)) =o[atTop] fun d : ℕ ↦ (d : ℝ) ^ 2 := by
  sorry

/-- It is easy to see that $f(d)\leq d^2+1$ using a greedy colouring. -/
@[category textbook, AMS 5]
theorem erdos_797.variants.greedy (d : ℕ) : f d ≤ d ^ 2 + 1 := by
  sorry

/-- Erdős had shown $f(d)\geq d^{4/3-o(1)}$. -/
@[category research solved, AMS 5]
theorem erdos_797.variants.erdos_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, (d : ℝ) ^ (4 / 3 - ε : ℝ) ≤ f d := by
  sorry

end Erdos797
