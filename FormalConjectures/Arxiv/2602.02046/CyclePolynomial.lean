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
# Real-rootedness of graphical cycle polynomials on chordal graphs

*References:*
- [M. Yaqubi and M. Mirzavaziri, On the Graphical r-Stirling Numbers of the First Kind for Specific Graph Families, version 1, Conjecture 6.2](https://arxiv.org/html/2602.02046v1)
- [A. R. Barghi, graphical cycle polynomial and fan enumeration, Theorem 2.5 (2018)](https://ajc.maths.uq.edu.au/pdf/70/ajc_v70_p253.pdf)
- [J. J. Gebendorfer, A chordal counterexample to graphical cycle polynomial real-rootedness, 12 October 2026; written disproof and source discrepancies](https://github.com/user-attachments/files/33357117/Gebendorfer_chordal_Intake_2026-10-12.zip)

We use edge-supported permutations: transpositions require edges and count once,
longer cycles have both orientations and need not be induced. The source's
omitted adjacency restatement and inconsistent wheel example are disclosed in
the cited source archive; alternative counting rules are not silently substituted.
-/

@[expose] public section
namespace YaqubiMirzavaziri.CyclePolynomial
open SimpleGraph Finset Polynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nontrivial permutation cycles plus fixed points, each counted once. -/
noncomputable def cycleCount (σ : Equiv.Perm V) : ℕ := by
  classical
  exact σ.cycleFactorsFinset.card + (univ.filter fun v => σ v = v).card

noncomputable def cyclePolynomial (G : SimpleGraph V) : Polynomial ℝ := by
  classical
  exact ∑ σ ∈ (univ : Finset (Equiv.Perm V)).filter
    (fun σ => ∀ v, σ v = v ∨ G.Adj v (σ v)), X ^ cycleCount σ

def IsRealRooted (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, p.eval₂ (algebraMap ℝ ℂ) z = 0 → z.im = 0

/-- The five-vertex fan, with universal vertex 4 and a path on 0,1,2,3. -/
def fanGraph : SimpleGraph (Fin 5) where
  Adj u v := u ≠ v ∧
    (u = 4 ∨ v = 4 ∨ Nat.dist u.val v.val = 1)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by simpa [Nat.dist_comm] using h))⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- The fan is split: 1,2,4 form a clique and 0,3 are independent.
In particular it is chordal, without enumerating induced cycles. -/
@[category test, AMS 5]
theorem fan_isChordal : fanGraph.IsChordal := by
  apply SimpleGraph.IsSplitGraph.isChordal
  refine ⟨({1, 2, 4} : Set (Fin 5)), ?_, ?_⟩
  · rw [SimpleGraph.isClique_iff]
    unfold Set.Pairwise fanGraph
    decide
  · rw [SimpleGraph.isIndepSet_iff]
    unfold Set.Pairwise fanGraph
    decide

/-- The coefficient obstruction for the quartic factor of the five-vertex fan.
If its four roots were real, their reciprocals would satisfy these
two Vieta identities. The sum of four nonnegative squares would be -1. -/
@[category API, AMS 5]
theorem fan_reciprocal_coefficient_obstruction
    (a b c d : ℝ)
    (hsum : a + b + c + d = -4)
    (hpairs : a*b + a*c + a*d + b*c + b*d + c*d = (13 : ℝ) / 2) : False := by
  have hsq : (a + b + c + d)^2 = (16 : ℝ) := by
    rw [hsum]
    norm_num
  nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1),
    sq_nonneg (c + 1), sq_nonneg (d + 1)]

/-- The unrestricted graphical cycle polynomial of a finite simple chordal
graph need not have only real roots. This does not concern the restricted
$r$-polynomial, stable partitions, or chordless-cycle enumeration. -/
@[category research solved, AMS 5]
theorem conjecture6_2 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.IsChordal → IsRealRooted (cyclePolynomial G) := by
  sorry

end YaqubiMirzavaziri.CyclePolynomial
