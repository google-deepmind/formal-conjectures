import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def IsDominatingSet (S : Finset V) : Prop := ∀ v ∉ S, ∃ u ∈ S, G.Adj v u

noncomputable def independentDominationNumber : ℕ :=
  ⨅ (S : Finset V) (_ : G.IsIndepSet S ∧ IsDominatingSet G S), S.card

variable (D := G.maxDegree) (i := independentDominationNumber G) (n := Fintype.card V)

theorem independentDominationEven (hIso : 0 < G.minDegree) (hMax : 1 ≤ D) (hEven : Even D) :
    (D + 2)^2 * i ≤ (D^2 + 4) * n := by
  sorry

theorem independentDominationOdd (hIso : 0 < G.minDegree) (hMax : 1 ≤ D) (hOdd : Odd D) :
    (D + 1) * (D + 3) * i ≤ (D^2 + 3) * n := by
  sorry
