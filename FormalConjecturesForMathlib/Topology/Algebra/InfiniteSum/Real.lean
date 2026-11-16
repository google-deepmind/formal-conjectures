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


public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Divergence of a nonnegative sum over a subset

Mathlib's `not_summable_iff_tendsto_nat_atTop_of_nonneg` relates `¬ Summable f` for
`f : ℕ → ℝ` to divergence of its partial sums. This states the same for a sum restricted
to a subset `A ⊆ ℕ`, in terms of the partial sums over `A`.
-/

open Filter

/-- For a nonnegative `f`, the sum over a subset `A` fails to be summable exactly when the
partial sums of `f` restricted to `A` diverge. -/
theorem not_summable_subtype_iff_tendsto_sum_indicator {A : Set ℕ} {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    ¬ Summable (fun n : A ↦ f n) ↔
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, A.indicator f n) atTop atTop := by
  have hcomp : (fun n : A ↦ f n) = f ∘ (Subtype.val) := rfl
  rw [hcomp, summable_subtype_iff_indicator,
    not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => Set.indicator_nonneg (fun a _ => hf a) n)]
