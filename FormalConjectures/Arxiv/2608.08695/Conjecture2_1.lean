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
# Maximal real projection constants: Conjecture 2.1

*Reference:* Beata Deregowska and Barbara Lewandowska,
*Maximal Projection Constants and Extremal Vector Configurations: Some Conjectures and Examples*,
[arXiv:2608.08695v1, Conjecture 2.1](https://arxiv.org/html/2608.08695v1#S2).
-/

@[expose] public section

namespace Arxiv.«2608.08695»

/-- A real matrix is admissible if its rows are orthonormal. -/
def IsAdmissible (m N : ℕ) (U : Matrix (Fin m) (Fin N) ℝ) : Prop :=
  U * U.transpose = 1

/-- A weight vector is admissible if its entries are nonnegative and if their squares sum to one. -/
def IsAdmissibleWeights (N : ℕ) (t : Fin N → ℝ) : Prop :=
  (∀ i : Fin N, 0 ≤ t i) ∧ (∑ i : Fin N, (t i) ^ 2) = 1

/-- The sum of absolute inner products between columns of 'U', weighted by the products of the corresponding entries of 't'. -/
noncomputable def F (m N : ℕ) (U : Matrix (Fin m) (Fin N) ℝ) (t : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, t i * t j * |(U.transpose * U) i j|

/-- The set of values of 'F' over all dimensions 'N >= m', admissible matrices, and admissible weight vectors. -/
def S (m : ℕ) : Set ℝ :=
  {x : ℝ | ∃ N : ℕ, m ≤ N ∧ ∃ U : Matrix (Fin m) (Fin N) ℝ, ∃ t : Fin N → ℝ, IsAdmissible m N U ∧ IsAdmissibleWeights N t ∧ F m N U t = x}

/-- The maximal real projection constant in dimension 'm' is defined as the supremum of 'S m' using the finite-matrix characterization. -/
noncomputable def lambdaR (m : ℕ) : ℝ :=
  sSup (S m)


/-- The maximal real projection constant in dimension 6 is $16/7$ -/
@[category research open, AMS 46]
theorem conjecture_six : lambdaR 6 = 16 / 7 := by sorry

/-- The maximal real projection constant in dimension 8 is $8/3$ -/
@[category research open, AMS 46]
theorem conjecture_eight : lambdaR 8 = 8 / 3 := by sorry

end Arxiv.«2608.08695»
