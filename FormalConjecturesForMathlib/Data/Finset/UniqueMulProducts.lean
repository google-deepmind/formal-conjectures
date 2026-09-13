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

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Image

@[expose] public section

namespace Finset

/-- The number of representations of `m` as `a * b` with `a ∈ A` and `b ∈ B`. -/
def mulRepresentationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  (A.product B).filter (fun p => p.1 * p.2 = m) |>.card

/-- The products `a * b` with `a ∈ A`, `b ∈ B` that have exactly one such representation. -/
def uniqueMulProducts (A B : Finset ℕ) : Finset ℕ :=
  ((A.product B).image (fun p => p.1 * p.2)).filter (fun m =>
    mulRepresentationCount A B m = 1)

@[simp]
lemma mulRepresentationCount_empty_left (B : Finset ℕ) (m : ℕ) :
    mulRepresentationCount ∅ B m = 0 := by
  simp [mulRepresentationCount]

@[simp]
lemma uniqueMulProducts_empty_left (B : Finset ℕ) :
    uniqueMulProducts ∅ B = ∅ := by
  simp [uniqueMulProducts]

@[simp]
lemma mulRepresentationCount_empty_right (A : Finset ℕ) (m : ℕ) :
    mulRepresentationCount A ∅ m = 0 := by
  simp [mulRepresentationCount]

@[simp]
lemma uniqueMulProducts_empty_right (A : Finset ℕ) :
    uniqueMulProducts A ∅ = ∅ := by
  simp [uniqueMulProducts]

lemma mulRepresentationCount_singleton (a b m : ℕ) :
    mulRepresentationCount {a} {b} m = if a * b = m then 1 else 0 := by
  simp [mulRepresentationCount, filter_singleton]
  split_ifs <;> simp

lemma uniqueMulProducts_singleton (a b : ℕ) :
    uniqueMulProducts {a} {b} = {a * b} := by
  simp [uniqueMulProducts, mulRepresentationCount_singleton]

end Finset
