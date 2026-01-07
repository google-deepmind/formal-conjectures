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
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 153

*References:*
 - [erdosproblems.com/153](https://www.erdosproblems.com/153)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
    Theory (1994), 329-347.
-/

open scoped Pointwise
open Filter Finset

/-- Suppose `A` is a finite Sidon set of size `n`. Then `(A + A).card = n.choose 2 + n`. -/
@[category API, AMS 5]
theorem IsSidon.add_card {A : Finset ℕ} {n : ℕ} (hn : A.card = n) (hA : IsSidon A) :
    (A + A).card = n.choose 2 + n := by
  sorry

namespace Erdos153

/-- Suppose `A` is a finite Sidon set of size `n`. We define `s` to be the increasing order
isomorphism between `Fin (n.choose 2 + n)` and `A + A`. -/
def s {A : Finset ℕ} {n : ℕ} (hn : A.card = n) (hA : IsSidon A) : Fin (n.choose 2 + n) → A + A :=
  (A + A).orderIsoOfFin (hA.add_card hn)

/-- Define `f n` to be the minimum of `∑ (s (i + 1) - s i) ^ 2 / n` as `A`
ranges over all Sidon sets of size `n`, where `s` is an order embedding from `Fin n` into `A`. -/
noncomputable def f (n : ℕ) : ℝ :=
  ⨅ A : {A : Finset ℕ | A.card = n ∧ IsSidon A},
  ∑ i : Set.Ico 1 (n.choose 2 + n),
  (s A.2.1 A.2.2 sorry - s A.2.1 A.2.2 sorry) ^ 2 / (n : ℝ)

end Erdos153
