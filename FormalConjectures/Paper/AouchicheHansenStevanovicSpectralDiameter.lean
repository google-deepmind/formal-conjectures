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
# Maximum adjacency spectral-radius–diameter product

*References:*
- [M. Aouchiche, P. Hansen, D. Stevanović, Variable neighborhood search for extremal graphs. 17. Further conjectures and results about the index, Conjecture 4.3 (2009)](https://doi.org/10.7151/dmgt.1430)
- [J. J. Gebendorfer, The maximum adjacency spectral radius–diameter product of a connected graph; undated manuscript archive](https://github.com/user-attachments/files/33357691/VNS17_Conjecture_4_3_Intake_2026-10-12.zip)
- [P. Hansen and D. Stevanović, On bags and bugs, fixed-diameter theorem](https://doi.org/10.1016/j.dam.2007.05.044)

A q-vertex attached path identifies one endpoint with a clique vertex and adds
q-1 new vertices. The fixed-diameter spectral classification and equality input
are credited in the written proof; a retrieved file date is not a publication date.
-/

@[expose] public section
namespace AouchicheHansenStevanovic.SpectralDiameter
open SimpleGraph

/-- Two attached paths with roots zero and one and disjoint new vertices. -/
def tailOne (p q₁ : ℕ) : List ℕ := 0 :: (List.range (q₁ - 1)).map (p + ·)
def tailTwo (p q₁ q₂ : ℕ) : List ℕ :=
  1 :: (List.range (q₂ - 1)).map (fun i => p + (q₁ - 1) + i)

/-- K_p minus edge 01, with the two paths attached at zero and one. -/
def bug (p q₁ q₂ : ℕ) : SimpleGraph (Fin (p + q₁ + q₂ - 2)) where
  Adj u v := u ≠ v ∧
    ((u.val < p ∧ v.val < p ∧ ¬ ((u.val = 0 ∧ v.val = 1) ∨
      (u.val = 1 ∧ v.val = 0))) ∨
    (u.val, v.val) ∈ (tailOne p q₁).zip (tailOne p q₁).tail ∨
    (v.val, u.val) ∈ (tailOne p q₁).zip (tailOne p q₁).tail ∨
    (u.val, v.val) ∈ (tailTwo p q₁ q₂).zip (tailTwo p q₁ q₂).tail ∨
    (v.val, u.val) ∈ (tailTwo p q₁ q₂).zip (tailTwo p q₁ q₂).tail)
  symm := ⟨by intro u v h; aesop⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

noncomputable def objective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  exact sSup (spectrum ℝ (G.adjMatrix ℝ)) * G.diam

/-- The bug in the original Conjecture 4.3 attains the maximum adjacency
spectral-radius times edge-diameter product at each connected order n>=3. -/
@[category research solved, AMS 5 15]
theorem conjecture4_3 (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) :
    objective G ≤ objective (bug (n / 2 + 2) ((n + 3) / 4) ((n + 1) / 4)) := by
  sorry

/-- The maximum is attained only by the indicated graph, up to isomorphism. -/
@[category research solved, AMS 5 15]
theorem equality_cases (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) :
    objective G = objective (bug (n / 2 + 2) ((n + 3) / 4) ((n + 1) / 4)) ↔
      Nonempty (G ≃g bug (n / 2 + 2) ((n + 3) / 4) ((n + 1) / 4)) := by
  sorry

end AouchicheHansenStevanovic.SpectralDiameter
