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
# Normalized reduced numerator of the score determinant

*References:*
- [Grosdos, Heaton, Kubjas, Kuznetsova, Scholten, Sorea, Exact solutions in log-concave maximum likelihood estimation, Definition 2.6 and Conjecture 3.4 (2023)](https://doi.org/10.1016/j.aam.2022.102448)
- [J. J. Gebendorfer, Exact poles and reduced numerators of score equation determinants, 8 September 2026, Theorem 2.1; manuscript and intake](https://github.com/google-deepmind/formal-conjectures/issues/7243)

We state the stronger positive-weight pure-complex theorem, which includes the
source's regular triangulations. The unit convention is D=product(delta_j).
The polynomial matrix B is exactly A diag(delta_j^2), obtained by the quotient
rule, so det(B)=N D expresses det(A)=N/D. Coprimality makes this a reduced
fraction with fixed denominator. Relative primality means common divisors are
units, without asserting a Bezout identity in this multivariate ring. The source's leading-degree argument is credited;
the reduced-denominator calculation is the additional written claim.
-/

@[expose] public section
namespace GrosdosEtAl.ScoreDeterminant
open Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One-skeleton neighbors of the specified facets. -/
noncomputable def neighbors (F : Finset (Finset V)) (j : V) : Finset V := by
  classical
  exact univ.filter fun i => i ≠ j ∧ ∃ σ ∈ F, i ∈ σ ∧ j ∈ σ

noncomputable def delta (F : Finset (Finset V)) (j : V) : MvPolynomial V ℝ :=
  ∏ i ∈ neighbors F j, (X j - X i)

noncomputable def leadingFactor (F : Finset (Finset V)) (w : Finset V → ℝ)
    (j : V) : MvPolynomial V ℝ := by
  classical
  exact ∑ σ ∈ F.filter (fun σ => j ∈ σ), C (w σ) *
    ∏ i ∈ neighbors F j \ σ, (X j - X i)

noncomputable def denominator (F : Finset (Finset V)) : MvPolynomial V ℝ :=
  ∏ j : V, delta F j

/-- Quotient-rule clearing of the defining score matrix, column by column. -/
noncomputable def clearedMatrix (F : Finset (Finset V)) (w : Finset V → ℝ) :
    Matrix V V (MvPolynomial V ℝ) := by
  classical
  exact fun i j => delta F j * pderiv i (leadingFactor F w j) -
    leadingFactor F w j * pderiv i (delta F j) +
    if i = j then leadingFactor F w j * delta F j else 0

/-- Twice the number of unordered edges, computed as the neighbor incidence sum. -/
noncomputable def twiceEdges (F : Finset (Finset V)) : ℕ := ∑ j : V, (neighbors F j).card

/-- With all facets of size d+1, all vertices used and all facet weights positive,
the exact normalized numerator is coprime to D, has degree 2e-nd, and its highest
homogeneous part is the product of the source's P_j. The numerical degree uses
natural subtraction; the pure-complex hypotheses guarantee 2e >= nd. -/
@[category research solved, AMS 13 15 52 62]
theorem positive_pure_complex (F : Finset (Finset V)) (d : ℕ)
    (w : Finset V → ℝ) (hn : 1 ≤ Fintype.card V)
    (hpure : ∀ σ ∈ F, σ.card = d + 1) (hused : ∀ j : V, ∃ σ ∈ F, j ∈ σ)
    (hw : ∀ σ ∈ F, 0 < w σ) :
    ∃ N : MvPolynomial V ℝ, denominator F ≠ 0 ∧
      N * denominator F = (clearedMatrix F w).det ∧
      IsRelPrime N (denominator F) ∧
      N.totalDegree = twiceEdges F - Fintype.card V * d ∧
      homogeneousComponent N.totalDegree N = ∏ j : V, leadingFactor F w j := by
  sorry

end GrosdosEtAl.ScoreDeterminant
