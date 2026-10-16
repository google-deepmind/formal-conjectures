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
# Clark's degree-dispersion conjecture

*References:*
- [G. J. Clark, Comparing Eigenvector and Degree Dispersion with the Principal Ratio of a Graph, version 1, Section 4, Conjecture 2 (1 February 2022)](https://arxiv.org/abs/2202.00325v1)
- [J. J. Gebendorfer, Degree dispersion and sharp universal bounds for Clark's irregularity measure, 7 September 2026, Theorem 2.1; manuscript archive](https://github.com/user-attachments/files/33357655/Clark_Conjecture_2_Intake_2026-10-12.zip)

The numerical bound also follows from de Caen's classical degree-square inequality.
The target here is Conjecture 2. The arbitrary-order fixed-order star assertion in
Conjecture 3 is not claimed to be solved by its separate endpoint bounds.
-/

@[expose] public section
namespace Clark.DegreeDispersion
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def dispersion (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (Fintype.card V : ℝ) * (∑ v : V, (G.degree v : ℝ)^2) /
    (4 * (G.edgeFinset.card : ℝ)^2) - 1

/-- A labeled graph is a star exactly when all its edges join a center to a
unique other vertex, and every other vertex is adjacent to that center. -/
def IsStar (G : SimpleGraph V) : Prop :=
  ∃ c : V, ∀ u v : V, G.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c)

/-- At every connected order $n\ge2$, the star maximizes squared degree
coefficient of variation. All subtractions in the numerical bound are real. -/
@[category research solved, AMS 5 15]
theorem conjecture2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 ≤ Fintype.card V) :
    dispersion G ≤ ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1)) := by
  sorry

/-- Equality holds exactly for stars, expressed independently of vertex labels. -/
@[category research solved, AMS 5 15]
theorem conjecture2_equality (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 ≤ Fintype.card V) :
    dispersion G = ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1)) ↔ IsStar G := by
  sorry

end Clark.DegreeDispersion
