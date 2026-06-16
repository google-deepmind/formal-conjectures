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

/-!
# Erdős Problem 448

*References:*
- [erdosproblems.com/448](https://www.erdosproblems.com/448)
- [Er79], [Er79e], [ErGr80, p.89], [Er81h, p.173]
- [ErTe81] Erdős, P., Tenenbaum, G., *Sur la structure de la suite des diviseurs d'un entier.*
  Ann. Inst. Fourier (Grenoble) **31** (1981), 17–37.
-/

namespace Erdos448

/-- `tauPlus n` (written `τ⁺(n)`) counts the number of `k` such that `n` has a divisor in
`[2^k, 2^{k+1})`. Equivalently, the number of distinct values `⌊log₂ d⌋` as `d` ranges over the
divisors of `n`: a divisor `d` lies in `[2^k, 2^{k+1})` iff `Nat.log 2 d = k`. -/
def tauPlus (n : ℕ) : ℕ := (n.divisors.image (Nat.log 2)).card

/-- Sanity check: `τ⁺(6) = 3`. Divisors `1,2,3,6` lie in dyadic blocks `k = 0,1,1,2`,
so the distinct blocks are `{0,1,2}`. (τ(6) = 4.) -/
@[category test, AMS 11]
theorem tauPlus_six : tauPlus 6 = 3 := by decide

/-- Sanity check: `τ⁺(12) = 4`. Divisors `1,2,3,4,6,12` lie in dyadic blocks `k = 0,1,1,2,2,3`,
so the distinct blocks are `{0,1,2,3}`. (τ(12) = 6.) -/
@[category test, AMS 11]
theorem tauPlus_twelve : tauPlus 12 = 4 := by decide

/-- Always `τ⁺(n) ≤ τ(n)`: the occupied dyadic blocks are the image of the divisor set under
`Nat.log 2`, and an image has at most as many elements as its source. This is what makes the
`ε < 1` comparison in the problem meaningful. -/
@[category test, AMS 11]
theorem tauPlus_le_tau (n : ℕ) : tauPlus n ≤ n.divisors.card :=
  Finset.card_image_le

/--
Let `τ(n)` count the divisors of `n` and `τ⁺(n)` count the number of `k` such that `n` has a
divisor in `[2^k, 2^{k+1})`. Is it true that, for all `ε > 0`,
$$ τ⁺(n) < ε · τ(n) $$
for almost all `n`?

The answer is **no**. This was disproved by Erdős and Tenenbaum [ErTe81], who showed that the
upper density of the set of such `n` is `≍ ε^{1-o(1)}` (the exponent `o(1) → 0` as `ε → 0`); in
particular this set does not have density `1` for small `ε`. A sharper bound `≪ ε log(2/ε)` and the
existence of a distribution function for `τ⁺(n)/τ(n)` were later established by Hall and
Tenenbaum [HaTe88, §4.6].
-/
@[category research solved, AMS 11]
theorem erdos_448 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.HasDensity 1 := by
  sorry

end Erdos448
