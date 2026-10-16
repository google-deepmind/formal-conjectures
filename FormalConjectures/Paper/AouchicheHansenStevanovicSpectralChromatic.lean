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
# Maximum of adjacency spectral radius minus chromatic number

*References:*
- [M. Aouchiche, P. Hansen, D. Stevanović, Variable neighborhood search for extremal graphs. 17. Further conjectures and results about the index, Table 1 (2009)](https://doi.org/10.7151/dmgt.1430)
- [J. J. Gebendorfer, Maximizing the Difference Between the Spectral Radius and the Chromatic Number, 7 August 2026; source package](https://github.com/user-attachments/files/33356664/VNS_Max_Rho_Minus_Chi_Intake_2026-10-12.zip)

The original table transcription is recorded in the cited source archive; the original
journal PDF was unavailable during that intake. The fixed-chromatic-number
spectral reduction is established literature and is not attributed as new here.
-/

@[expose] public section
namespace AouchicheHansenStevanovic.SpectralChromatic
open SimpleGraph

/-- The largest adjacency eigenvalue. For a finite undirected graph this is its
nonnegative adjacency spectral radius. -/
noncomputable def rho {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup (spectrum ℝ (G.adjMatrix ℝ))

noncomputable def objective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  rho G - G.chromaticNumber.toNat

/-- The least eligible number of parts whose adjacent product reaches $n$.
Using a bounded infimum over naturals preserves the lower cutoff $k\ge2$. -/
noncomputable def kappa (n : ℕ) : ℕ := sInf {k : ℕ | 2 ≤ k ∧ n ≤ k * (k + 1)}

/-- The printed balanced $\lceil\sqrt n\rceil$-partite candidate does not
maximize $\rho-\chi$ at every connected order $n\ge3$. -/
@[category research solved, AMS 5]
theorem table1_upper : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj], 3 ≤ n → G.Connected →
    objective G ≤ objective (turanGraph n (⌈Real.sqrt n⌉₊)) := by
  sorry

/-- The corrected candidate maximizes the objective for every connected graph
of order $n\ge3$. -/
@[category research solved, AMS 5]
theorem corrected_maximum (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) :
    objective G ≤ objective (turanGraph n (kappa n)) := by
  sorry

/-- The equality set consists of the corrected Turán graph, with the adjacent
part-count graph as an additional possibility exactly at $n=\kappa(\kappa+1)$.
This is an isomorphism statement, not equality of labeled graphs. -/
@[category research solved, AMS 5]
theorem equality_cases (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) :
    objective G = objective (turanGraph n (kappa n)) ↔
      Nonempty (G ≃g turanGraph n (kappa n)) ∨
        (n = kappa n * (kappa n + 1) ∧
          Nonempty (G ≃g turanGraph n (kappa n + 1))) := by
  sorry

end AouchicheHansenStevanovic.SpectralChromatic
