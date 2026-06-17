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
- [Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
- [Er79e] Erdős, Paul, Some unconventional problems in number theory. Astérisque (1979), 73-82. 
- [HaTe88] Hall, Richard R. and Tenenbaum, Gérald, Divisors. (1988), xvi+167. 
- [ErTe81] Erdős, P., Tenenbaum, G., *Sur la structure de la suite des diviseurs d'un entier.*
  Ann. Inst. Fourier (Grenoble) **31** (1981), 17–37.
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval.*
  Ann. of Math. (2) **168** (2008), 367–433.
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

open Filter Asymptotics Topology

/--
Quantitative form of the (negative) answer to `erdos_448`. Erdős and Tenenbaum [ErTe81] showed that
the upper density of `{n | τ⁺(n) < ε·τ(n)}` is in fact `≍ ε^{1-o(1)}`, where the `o(1)` in the
exponent tends to `0` as `ε → 0`. Equivalently, `log (upperDensity …) / log ε → 1` as `ε → 0⁺`. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.erdos_tenenbaum :
    Tendsto
      (fun ε : ℝ =>
        Real.log ({n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.upperDensity) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  sorry

/--
A more precise result of Hall and Tenenbaum [HaTe88, §4.6]: the upper density of
`{n | τ⁺(n) < ε·τ(n)}` is `≪ ε·log(2/ε)` as `ε → 0⁺`. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.hall_tenenbaum_upper_bound :
    (fun ε : ℝ => ({n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}).upperDensity)
      =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ε * Real.log (2 / ε)) := by
  sorry

/--
Hall and Tenenbaum [HaTe88, §4.6] further prove that `τ⁺(n)/τ(n)` has a distribution function:
there is a function `F` such that, for every `z`, the set `{n | τ⁺(n)/τ(n) ≤ z}` has density `F z`. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.hall_tenenbaum_distribution :
    ∃ F : ℝ → ℝ, ∀ z : ℝ,
      {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z}.HasDensity (F z) := by
  sorry

/-- The exponent in Ford's estimate below: `α = 1 - (1 + log log 2)/log 2 = 0.08607…`. -/
noncomputable def fordExponent : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2

/--
Erdős and Graham asked whether there is a good inequality for `∑_{n ≤ x} τ⁺(n)`. This was answered
by Ford [Fo08], who proved
`∑_{n ≤ x} τ⁺(n) ≍ x·(log x)^{1-α}/(log log x)^{3/2}`,
where `α = 1 - (1 + log log 2)/log 2 = 0.08607…` (see `fordExponent`). -/
@[category research solved, AMS 11]
theorem erdos_448.variants.ford :
    (fun x : ℕ => ∑ n ∈ Finset.Icc 1 x, (tauPlus n : ℝ))
      =Θ[atTop]
      (fun x : ℕ =>
        (x : ℝ) * Real.log (x : ℝ) ^ (1 - fordExponent)
          / Real.log (Real.log (x : ℝ)) ^ ((3 : ℝ) / 2)) := by
  sorry

end Erdos448
