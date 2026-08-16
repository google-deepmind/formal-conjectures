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

import FormalConjecturesUtil

/-!
# Generalized Bessel numbers

The generalized Bessel numbers $a(n)$ are defined by the continued fraction
$$G(x) = \frac{1}{1 - x - \frac{x^2}{1 - 0x - \frac{x^2}{1 - 2x - \frac{x^2}{1 - 0x - \dots}}}}.$$
In the associated weighted Motzkin path model from height 0 to height 0, the level step weights
are $\alpha_0 = 1$ and for $k \ge 1$, $\alpha_k = k/2 + 1$ if $k$ is even and $0$ if $k$ is odd.

*References:*
- [A145062](https://oeis.org/A145062)
- Yan X Zhang, "Four Variations on Graded Posets", arXiv preprint
  [arXiv:1508.00318](https://arxiv.org/abs/1508.00318) [math.CO], 2015.-/

namespace OeisA145062

/-- Level step weights for the Motzkin path model. -/
def b (k : ℕ) : ℕ :=
  if k = 0 then 1
  else if k % 2 = 0 then k / 2 + 1
  else 0

/-- Single-step transition for the Motzkin path state vector. -/
def step (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  f (k + 1) + (if k = 0 then 0 else f (k - 1)) + b k * f k

/-- Auxiliary function where `aux n k` is the weight of paths of length `n` ending at height `k`. -/
def aux : ℕ → ℕ → ℕ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => step (aux n)

/-- The generalized Bessel numbers $a(n)$. -/
def a (n : ℕ) : ℕ := aux n 0

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 12 := by decide

/-- Sequence $s(n)$ seen in Fig. 8 of Zhang (2015). -/
axiom sequenceS : ℤ → ℕ

/--
"Is this the same as the sequence s(n) that can be seen in Fig. 8 of Zhang (2015),
with a different offset?"-/
@[category research open, AMS 5 11]
theorem conjecture : ∃ k : ℤ, ∀ n : ℕ, a n = sequenceS (n + k) := by
  sorry

end OeisA145062
