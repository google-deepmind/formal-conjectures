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
# Erdős Problem 84

*References:*
- [erdosproblems.com/84](https://www.erdosproblems.com/84)
- [Ve04] Verstraëte, Jacques, On the number of sets of cycle lengths.
  Combinatorica (2004), 719–730.
-/

@[expose] public section

namespace Erdos84

open Filter Asymptotics

/-- The number of distinct cycle sets of graphs on $n$ vertices. -/
noncomputable def cycleSetCount (n : ℕ) : ℕ :=
  (Set.range fun G : SimpleGraph (Fin n) => G.cycleLengths).ncard

@[category test, AMS 5]
theorem cycleSetCount_pos (n : ℕ) : 0 < cycleSetCount n := by
  exact (Set.ncard_pos (Set.finite_range _)).2 ⟨_, ⟨⊥, rfl⟩⟩

@[category test, AMS 5]
theorem cycleSetCount_of_le_two {n : ℕ} (hn : n ≤ 2) : cycleSetCount n = 1 := by
  have h : ∀ G : SimpleGraph (Fin n), G.cycleLengths = ∅ := by
    intro G
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro m ⟨v, p, hp, rfl⟩
    have hmin := hp.isCircuit.three_le_length
    have hmax := hp.support_nodup.length_le_card
    simp only [List.length_tail, SimpleGraph.Walk.length_support, Nat.add_sub_cancel,
      Fintype.card_fin] at hmax
    omega
  simp [cycleSetCount, h, Set.range_const]

/--
The cycle set of a graph $G$ on $n$ vertices is a set $A\subseteq \{3,\ldots,n\}$ such that
there is a cycle in $G$ of length $\ell$ if and only if $\ell \in A$. Let $f(n)$ count the
number of possible such $A$.

Prove that $f(n)=o(2^n)$.

The first problem was solved by Verstraëte [Ve04], who proved
$f(n)\ll 2^{n-n^{1/10}}$.
-/
@[category research solved, AMS 5]
theorem erdos_84.parts.i :
    (fun n => (cycleSetCount n : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) := by
  sorry

/-- Prove that $f(n)/2^{n/2}\to \infty$. -/
@[category research open, AMS 5]
theorem erdos_84.parts.ii :
    Tendsto (fun n => (cycleSetCount n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2))
      atTop atTop := by
  sorry

end Erdos84
