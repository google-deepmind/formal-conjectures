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
# The first nonzero term of Zudilin's normalized Hankel determinant

At $x=z=1$, Zudilin's normalized moments define an integer formal power series
$H_N$ whose exact order is $E_N=N(N-1)(2N-1)/6$ and whose first coefficient is
$(N!)^2(N+1)!/2^N$ [Co26].

Zudilin proved the lower bound for this order in a more general setting [Zu16,
Section 4]. The exact order and coefficient below concern each fixed rank $N$.
They do not assert an asymptotic as the rank tends to infinity at a fixed real
base, and give no irrationality conclusion for rational bases.

*References:*
- [Co26] W. Cook, *Hankel Determinants of Geometric Moments and Rational Lambert
  Values*, theorem "the first nonzero term of the Hankel determinant",
  [source](https://github.com/wcook04/plectis-erdos/blob/6db987f4a843ae40ab07ac782ef0cca1a95815c1/paper/1049/erdos-1049-rational-base-lambert.tex#L579-L627).
- [Zu16] W. Zudilin, *On the irrationality of generalized q-logarithm*,
  Research in Number Theory 2 (2016), Article 15,
  [arXiv:1601.02688v2](https://arxiv.org/abs/1601.02688v2), Section 4.
-/

@[expose] public section

open scoped BigOperators

namespace ZudilinHankelInitialTerm

/-- The finite formal q-Pochhammer product. -/
noncomputable def pochhammer (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

/-- The unit factor of the tth normalized moment summand at x = z = 1. -/
noncomputable def normalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  pochhammer 1 n ^ 3 * pochhammer (t + 1) n *
    PowerSeries.invOfUnit (pochhammer (n + 1 + t) (n + 1)) 1

/-- The tth normalized moment summand. -/
noncomputable def normalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * normalizedTailUnit n t

/-- Zudilin's normalized moment at x = z = 1. Each coefficient is a finite sum. -/
noncomputable def normalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (normalizedTail n t)

/-- The normalized Hankel determinant; the determinant at rank zero is one. -/
noncomputable def hankelDet (N : ℕ) : PowerSeries ℤ :=
  Matrix.det (fun i j : Fin N => normalizedMoment ((i : ℕ) + (j : ℕ)))

/-- For the normalized Hankel determinant $H_N$ at $x=z=1$, let
$E_N=N(N-1)(2N-1)/6$. Then
$$
  \operatorname{ord}_q H_N=E_N,\qquad
  2^N[q^{E_N}]H_N=(N!)^2(N+1)!.
$$
This is a statement about integer formal power series at each rank.
Rank zero uses the empty determinant and has order zero and coefficient one.
-/
@[category research solved, AMS 11 15,
  formal_proof using lean4 at "https://github.com/wcook04/plectis-erdos-lean/blob/01b23a6e0ead0a80b89dd1b3dffed1e4356ad2ba/verification/FC1049OrderCoeffCurrent/FC1049OrderCoeffSolution.lean#L36-L47"]
theorem first_nonzero_term (N : ℕ) :
    PowerSeries.order (hankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) ∧
    (2 : ℤ) ^ N * PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (hankelDet N) = (N.factorial : ℤ) ^ 2 * ((N + 1).factorial : ℤ) := by
  sorry

end ZudilinHankelInitialTerm
