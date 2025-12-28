/-
Copyright 2025 The Formal Conjectures Authors.

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

open Finset Real

/-!
# Erdős Problem 1084

*Reference:* [erdosproblems.com/1084](https://www.erdosproblems.com/1084)

Let `f_d(n)` be the maximum number of pairs of points at distance exactly `1`
among any set of `n` points in `ℝ^d`, under the condition that all pairwise
distances are at least `1`.

Estimate the growth of `f_d(n)`.

Status: open.
-/

namespace Erdos1084

/--
Erdős problem 1084.

For every dimension `d`, there exists a function `f : ℕ → ℕ` such that for any
finite set `s` of points in `ℝ^d` with all pairwise distances at least `1`,
the number of unordered pairs of distinct points in `s` at distance exactly `1`
is at most `f (card s)`.
-/
@[category research open, AMS 52]
theorem erdos_1084 :
  ∀ d : ℕ,
    ∃ f : ℕ → ℕ,
      ∀ s : Finset (EuclideanSpace ℝ (Fin d)),
        (∀ ⦃x y⦄, x ∈ s → y ∈ s → x ≠ y → dist x y ≥ 1) →
        ((s.product s).filter
          (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card ≤ f s.card := by
  sorry

end Erdos1084
