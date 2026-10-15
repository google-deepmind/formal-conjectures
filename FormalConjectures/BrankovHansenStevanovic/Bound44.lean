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
# Restricted variants of Brankov–Hansen–Stevanović Bound 44

*References:*
- [V. Brankov, P. Hansen, D. Stevanović, Automated conjectures on upper bounds for the largest Laplacian eigenvalue of graphs, Bound 44 (2006)](https://doi.org/10.1016/j.laa.2005.10.017)
- [J. J. Gebendorfer, Bound 44 Below Signless Radius Eleven: Exact Integer Collatz–Wielandt Certificates, and Bound 44 on the Degree-{1,b} Class: An Edge-Bound Reduction and a Perron–Core Refinement, 24 August 2026; manuscripts and intake](https://github.com/google-deepmind/formal-conjectures/issues/7282)

These are two restricted infinite regions, not a resolution of unrestricted
Bound 44 or Bound 46. The finite type-space argument, known edge/Collatz bounds,
and their computer-assisted proof carriers are distinguished in the manuscripts.
-/

@[expose] public section
namespace BrankovHansenStevanovic.Bound44
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def laplacianMaximum (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup (spectrum ℝ (G.lapMatrix ℝ))

noncomputable def signlessMaximum (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup (spectrum ℝ (G.degMatrix ℝ + G.adjMatrix ℝ))

noncomputable def neighborMean (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℝ :=
  (∑ w ∈ G.neighborFinset v, (G.degree w : ℝ)) / G.degree v

noncomputable def edgeValue (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℝ :=
  ((G.degree u : ℝ) - 1)^2 + ((G.degree v : ℝ) - 1)^2 +
    neighborMean G u * neighborMean G v - (G.degree u : ℝ) * G.degree v

noncomputable def edgeMaximum (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {x : ℝ | ∃ u v, G.Adj u v ∧ x = edgeValue G u v}

/-- Bound 44 holds throughout the region of signless radius at most eleven. -/
@[category research solved, AMS 5 15]
theorem signless_at_most_eleven (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 ≤ Fintype.card V) (hq : signlessMaximum G ≤ 11) :
    laplacianMaximum G ≤ 2 + Real.sqrt (2 * edgeMaximum G) := by
  sorry

/-- The stronger finite type-space theorem yields both the exact rational
signless bound and the signless version of the radical inequality. -/
@[category research solved, AMS 5 15]
theorem finite_type_region (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 ≤ Fintype.card V)
    (hd : G.maxDegree ≤ 8) (hR : edgeMaximum G < 81 / 2) :
    signlessMaximum G ≤ 4275 / 389 ∧
      signlessMaximum G ≤ 2 + Real.sqrt (2 * edgeMaximum G) := by
  sorry

/-- The degree-{1,b} class satisfies the stronger signless bound, for arbitrary
integer $b\ge1$ without order, spectral-radius or bipartiteness restrictions. -/
@[category research solved, AMS 5 15]
theorem degree_one_b (b : ℕ) (hb : 1 ≤ b) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 ≤ Fintype.card V)
    (hd : ∀ v, G.degree v = 1 ∨ G.degree v = b) :
    signlessMaximum G ≤ 2 + Real.sqrt (2 * edgeMaximum G) ∧
      laplacianMaximum G ≤ 2 + Real.sqrt (2 * edgeMaximum G) := by
  sorry

end BrankovHansenStevanovic.Bound44
