/-
Copyright 2025 The Formal Conjectures Authors

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
# Main conjecture on fusible numbers

*Reference:* [Fusible numbers and Peano Arithmetic](https://arxiv.org/abs/2003.14342),
by Jeff Erickson, Gabriel Nivasch, and Junyan Xu.
Logical Methods in Computer Science, Volume 18, Issue 3 (July 28, 2022) lmcs:8555
-/

inductive IsFusible : ℚ → Prop
  | zero : IsFusible 0
  | fuse (a b : ℚ) : IsFusible a → IsFusible b → |a - b| < 1 → IsFusible ((a + b + 1) / 2)

/-- If `x` is a fusible number and `y` is its successor, then the interval `[x + 1, y + 1)` can be
divided into intervals `[ℓₙ, ℓₙ₊₁)`, such that the fusible numbers in `[ℓₙ, ℓₙ₊₁)` are obtained by
fusing the `n + 1`st successor of `x` with a fusible number.
This formalization differs from Conjecture 7.1 in the paper in four ways:
(1) it is obtained from Conjecture 7.1 by plugging in `n + 1` into `n`, which simplifies the expressions
  and removes the need to assume `n ≥ 1`;
(2) the `n + 1`st successor `s^(n+1)(x)` is replaced by the explicit value `x + (2 - 1 / 2 ^ n) * m`;
(3) instead of defining `y` to be the successor of `x`, we assert that there is no fusible number between `x` and `y`;
(4) instead of using `∃ z, IsFusible z ∧ q = s^(n+1)(x) ~ z` we use the value of `z` determined by the equality,
  namely `z = 2 * q - 1 - s^(n+1)(x)`, and it is easy to see `z ∈ [x + 1 - m / 2 ^ n, x + 1)` as required. -/
@[category research open, AMS 05]
theorem conj_7_1 (x y q : ℚ) (n : ℕ) (fus_x : IsFusible x) (fus_y : IsFusible y) (lt : x < y)
    (nmem_Icc : ∀ z, IsFusible z → z ∉ Set.Icc x y) :
    let m := y - x
    let ℓ (n : ℕ) := y + 1 - m / 2 ^ n
    IsFusible q → q ∈ Set.Ico (ℓ n) (ℓ (n + 1)) → IsFusible (2 * q - 1 - x - (2 - 1 / 2 ^ n) * m) := by
  sorry
