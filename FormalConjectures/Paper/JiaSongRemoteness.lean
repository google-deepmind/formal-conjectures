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
# Jia–Song remoteness plus second distance eigenvalue

*References:*
- [Jia and Song, Conjecture 3.8 (2018)](https://doi.org/10.1186/s13660-018-1663-5)
- [J. J. Gebendorfer, Remoteness Plus the Second Distance Eigenvalue: Counterexamples and an Exact Extremal Theorem, v2, 24 August 2026; manuscript, prior report and source archive](https://github.com/user-attachments/files/33368385/Jia_Intake_Gebendorfer_2026-10-13.zip)

The earlier public report of the bowtie/two-clique counterfamily dated 6 August
2026 is disclosed in the intake; no exclusive first-disproof claim is made.
The corrected domain includes K_n-e, unlike the original excluded domain.
The known Liu–Xue–Guo structural classification is credited in the written proof.
-/

@[expose] public section
namespace JiaSong
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def distanceMatrix (G : SimpleGraph V) : Matrix V V ℝ :=
  fun u v => G.dist u v

/-- Position one in the antitone eigenvalue enumeration, counted with multiplicity.
The zero default is irrelevant on the theorem domains of order at least four. -/
noncomputable def secondDistanceEigenvalue (G : SimpleGraph V) : ℝ :=
  let h : (distanceMatrix G).IsHermitian := by
    apply Matrix.ext
    intro i j
    simp [Matrix.conjTranspose_apply, distanceMatrix, SimpleGraph.dist_comm]
  (List.ofFn h.eigenvalues₀).getD 1 0

noncomputable def remoteness (G : SimpleGraph V) : ℝ :=
  sSup {x : ℝ | ∃ v : V, x = (∑ w : V, (G.dist v w : ℝ)) / ((Fintype.card V : ℝ) - 1)}

noncomputable def objective (G : SimpleGraph V) : ℝ :=
  remoteness G + secondDistanceEigenvalue G

noncomputable def conjecturedBound (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) - 1) +
    ((n : ℝ) - 1 - Real.sqrt (((n : ℝ) - 1)^2 + 8)) / 2

/-- One universal vertex joined to two disjoint cliques of balanced sizes. -/
def twoCliqueJoin (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val = 0 ∨ v.val = 0 ∨
    (u.val ≤ (n - 1) / 2 ∧ v.val ≤ (n - 1) / 2) ∨
    ((n - 1) / 2 < u.val ∧ (n - 1) / 2 < v.val))
  symm := ⟨by intro u v h; aesop⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- The original lower bound fails on connected graphs of order at least four
with at least two missing edges, exactly excluding K_n and K_n-e. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/RhudeJJJJ/formal-conjectures/blob/7a18fe152ccd0b109cc788c337dd7c3c04f8c975/Proofs/JiaSong/Full.lean#L28"]
theorem conjecture3_8 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    4 ≤ n → G.Connected → 2 ≤ n.choose 2 - G.edgeFinset.card →
      conjecturedBound n ≤ objective G := by
  sorry

/-- The corrected minimum at every order at least nine is attained at H_n.
Its domain includes K_n-e and excludes only complete graphs. -/
@[category research solved, AMS 5 15]
theorem corrected_minimum (n : ℕ) (hn : 9 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) (hnc : G ≠ ⊤) :
    objective (twoCliqueJoin n) ≤ objective G := by
  sorry

/-- The corrected minimizer is unique up to graph isomorphism. -/
@[category research solved, AMS 5 15]
theorem corrected_equality (n : ℕ) (hn : 9 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) (hnc : G ≠ ⊤) :
    objective G = objective (twoCliqueJoin n) ↔ Nonempty (G ≃g twoCliqueJoin n) := by
  sorry

end JiaSong
