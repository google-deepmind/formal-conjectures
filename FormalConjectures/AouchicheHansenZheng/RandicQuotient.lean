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
# Randić index divided by algebraic connectivity

*References:*
- M. Aouchiche, P. Hansen and M. Zheng, Variable neighborhood search for extremal graphs. 19. Further conjectures and results about the Randić index, Conjecture 4 (2007).
- [X. Li, Y. Shi and L. Wang, On a Relation Between Randić Index and Algebraic Connectivity, Conjecture 1.1 (2012), p. 845](https://match.pmf.kg.ac.rs/electronic_versions/Match68/n3/match68n3_843-849.pdf)
- [J. J. Gebendorfer, A Sharp Tadpole Threshold for the Randić Index–Algebraic Connectivity Ratio, 6 August 2026; written proof and intake](https://github.com/google-deepmind/formal-conjectures/issues/7253)

The printed conjecture has order at least THREE, as verified in the primary
2012 restatement; the intake's order-two cutoff is corrected here. The path
formula displayed below does not apply at order two. The sharp threshold 41
is within the tadpole family only; no global minimum-order claim is included.
-/

@[expose] public section
namespace AouchicheHansenZheng.RandicQuotient
open SimpleGraph

/-- Half the oriented edge sum counts each undirected edge once. -/
noncomputable def randic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ u : V, ∑ v : V, if G.Adj u v then
    1 / Real.sqrt ((G.degree u : ℝ) * G.degree v) else 0) / 2

/-- On connected graphs of order at least two the smallest positive Laplacian
eigenvalue is precisely the second-smallest eigenvalue, counted with multiplicity. -/
noncomputable def algebraicConnectivity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf {x : ℝ | x ∈ spectrum ℝ (G.lapMatrix ℝ) ∧ 0 < x}

noncomputable def quotient {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  randic G / algebraicConnectivity G

noncomputable def pathBound (n : ℕ) : ℝ :=
  ((n : ℝ) - 3 + 2 * Real.sqrt 2) / (4 * (1 - Real.cos (Real.pi / n)))

/-- The actual graph $P_n+\{0,2\}$, with path-order vertex labels. -/
def tadpole (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
    (u.val = 0 ∧ v.val = 2) ∨ (v.val = 0 ∧ u.val = 2))
  symm := ⟨by
    intro u v h
    refine ⟨Ne.symm h.1, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

noncomputable instance (n : ℕ) : DecidableRel (tadpole n).Adj := Classical.decRel _

/-- The quotient clause of Conjecture 4 is false even on its original domain
of connected finite simple graphs of order at least three. -/
@[category research solved, AMS 5 15]
theorem conjecture4_quotient : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj], 3 ≤ n → G.Connected → quotient G ≤ pathBound n := by
  sorry

/-- Every tadpole of order at least 41 exceeds the conjectured path bound. -/
@[category research solved, AMS 5 15]
theorem tadpole_counterfamily (n : ℕ) (hn : 41 ≤ n) :
    pathBound n < quotient (tadpole n) := by
  sorry

/-- Orders three through forty lie strictly below the bound in this family. -/
@[category research solved, AMS 5 15]
theorem tadpole_below_threshold (n : ℕ) (hn : 3 ≤ n) (h40 : n ≤ 40) :
    quotient (tadpole n) < pathBound n := by
  sorry

end AouchicheHansenZheng.RandicQuotient
