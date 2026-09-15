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

import FormalConjecturesUtil

/-!
# The burning number conjecture

*References:*
* [BJR16] Bonato, A., Janssen, J., and Roshanbin, E. (2016). "How to burn a graph."
  *Internet Math.* 12, pp. 85--100.
  [arXiv:1507.06524](https://arxiv.org/abs/1507.06524)
* [NT25] Norin, S. and Turcotte, J. (2025). "The burning number conjecture holds
  asymptotically." *J. Combin. Theory Ser. B* 171, pp. 208--235.
  [arXiv:2207.04035](https://arxiv.org/abs/2207.04035)
-/

namespace BurningNumberConjecture

variable {V : Type*}

/-- `x` is a **burning sequence** for `G`: fires started at `x 0, x 1, …` in successive rounds,
each spreading to all neighbours every round, burn every vertex of `G` within `k` rounds.
Equivalently, every vertex is within distance `k - 1 - i` of the `i`-th source. -/
def IsBurningSequence (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ v, ∃ i, G.Reachable (x i) v ∧ G.dist (x i) v + (i : ℕ) < k

/-- The **burning number** `b(G)`: the least number of rounds needed to burn every vertex
of `G`. -/
noncomputable def burningNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ x : Fin k → V, IsBurningSequence G x}

/-- On a nonempty graph, at least one round is needed. -/
@[category API, AMS 5]
lemma one_le_burningNumber [Nonempty V] (G : SimpleGraph V)
    (h : {k | ∃ x : Fin k → V, IsBurningSequence G x}.Nonempty) :
    1 ≤ burningNumber G := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h' | h'
  · obtain ⟨x, hx⟩ := h'
    obtain ⟨i, -⟩ := hx (Classical.arbitrary V)
    exact i.elim0
  · rw [h'] at h
    exact Set.not_nonempty_empty h

/--
**The burning number conjecture** (Bonato–Janssen–Roshanbin [BJR16]).

Every connected graph on `n` vertices can be burned in at most `⌈√n⌉` rounds: fires started at
one new vertex per round, each spreading to all neighbouring vertices every round, can burn
the whole graph in `⌈√n⌉` rounds.
-/
@[category research open, AMS 5]
theorem burning_number_conjecture {V : Type} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) :
    burningNumber G ≤ ⌈Real.sqrt (Fintype.card V)⌉₊ := by
  sorry

/--
**Paths attain the conjectured bound** (Bonato–Janssen–Roshanbin [BJR16]).

The burning number of the path on `n ≥ 1` vertices is exactly `⌈√n⌉`, so the bound in the
burning number conjecture cannot be improved.
-/
@[category research solved, AMS 5]
theorem burning_number_conjecture.variants.path (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (SimpleGraph.pathGraph n) = ⌈Real.sqrt n⌉₊ := by
  sorry

/--
**Norin–Turcotte (2025): the burning number conjecture holds asymptotically.**

For every `ε > 0`, every sufficiently large connected graph on `n` vertices can be burned in
at most `(1 + ε) √n` rounds.

*Reference:* [NT25].
-/
@[category research solved, AMS 5]
theorem burning_number_conjecture.variants.norin_turcotte (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V) := by
  sorry

/--
**A graph with one vertex burns in one round.**
-/
@[category test, AMS 5]
theorem burning_number_conjecture.variants.unique [Unique V] (G : SimpleGraph V) :
    burningNumber G = 1 := by
  have h : IsBurningSequence G (fun _ : Fin 1 => default) := by
    intro v
    have hv : v = default := Unique.eq_default v
    subst hv
    exact ⟨0, SimpleGraph.Reachable.refl _, by simp⟩
  exact le_antisymm (Nat.sInf_le ⟨_, h⟩) (one_le_burningNumber G ⟨1, _, h⟩)

/--
**Complete graphs burn in at most two rounds.**

The first fire spreads to every vertex in the second round.
-/
@[category test, AMS 5]
theorem burning_number_conjecture.variants.complete [Nonempty V] :
    burningNumber (⊤ : SimpleGraph V) ≤ 2 := by
  refine Nat.sInf_le ⟨fun _ => Classical.arbitrary V, fun v => ?_⟩
  by_cases hv : Classical.arbitrary V = v
  · subst hv
    exact ⟨0, SimpleGraph.Reachable.refl _, by simp⟩
  · have hadj : (⊤ : SimpleGraph V).Adj (Classical.arbitrary V) v := hv
    have hd := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    refine ⟨0, ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩, ?_⟩
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hd
    simpa using Nat.lt_succ_of_le hd

end BurningNumberConjecture
