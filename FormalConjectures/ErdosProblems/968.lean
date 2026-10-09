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
# Erdős Problem 968

Let `uₙ = pₙ / n`, where `pₙ` is the `n`th prime. Does the set of `n` such that `uₙ < uₙ₊₁`
have positive lower density?

Erdős and Prachar also proved that `∑_{pₙ < x} |uₙ₊₁ - uₙ| ≍ (log x)^2`, and that the set of `n`
such that `uₙ > uₙ₊₁` has positive lower density. Erdős also asked whether there are infinitely many
increasing triples `uₙ < uₙ₊₁ < uₙ₊₂` or decreasing triples `uₙ > uₙ₊₁ > uₙ₊₂`.

*Reference:* [erdosproblems.com/968](https://www.erdosproblems.com/968)

[ErPr61] Erdős, P. and Prachar, K., _Sätze und Probleme über pₖ/k_. Abh. Math. Sem. Univ. Hamburg
(1961/62), 251–256.

[FMT18] Ford, K. and Maynard, J. and Tao, T., _Chains of large gaps between primes_. Irregularities
in the distribution of prime numbers, Springer (2018), 1–21.

[Ma15] Maynard, J., _Small gaps between primes_. Ann. of Math. (2015), 383–413.
-/

@[expose] public section

open Filter Real
open scoped BigOperators

namespace Erdos968

/--
`u n` is the normalized `n`th prime, defined as `pₙ / (n+1)` where `pₙ` is the `n`th prime
(with `0.nth Nat.Prime = 2`).

This corresponds to the classical sequence `(p₁/1, p₂/2, p₃/3, ...)` while using `Nat.nth Prime`'s
`0`-based indexing; in particular, the denominator is always positive.
-/
noncomputable def u (n : ℕ) : ℝ :=
  (n.nth Nat.Prime : ℝ) / (n + 1)

/--
Does the set `{n | u n < u (n+1)}` have positive lower density?
-/
@[category research open, AMS 11]
theorem erdos_968 : answer(sorry) ↔ 0 < {n : ℕ | u n < u (n + 1)}.lowerDensity := by
  sorry

/--
Erdős and Prachar proved `∑_{pₙ < x} |u (n+1) - u n| ≍ (log x)^2` (see [ErPr61]).

We encode `∑_{pₙ < x}` as a sum over `n < Nat.primeCounting' x` (the number of primes `< x`).
-/
@[category research solved, AMS 11]
theorem erdos_968.variants.sum_abs_diff_isTheta_log_sq :
    (fun x : ℕ =>
        ∑ n < Nat.primeCounting' x, |u (n + 1) - u n|) =Θ[atTop]
      fun x : ℕ => log x ^ 2 := by
  sorry

/--
Erdős and Prachar proved that the set `{n | u n > u (n+1)}` has positive lower density
(see [ErPr61]).
-/
@[category research solved, AMS 11]
theorem erdos_968.variants.decreasing_steps_pos_lower_density :
    0 < {n : ℕ | u n > u (n + 1)}.lowerDensity := by
  sorry

/--
Erdős asked whether there are infinitely many solutions to `uₙ < uₙ₊₁ < uₙ₊₂`.

The answer is yes. Since `uₙ < uₙ₊₁` is equivalent to `pₙ₊₁ - pₙ > pₙ / n`, it suffices to have
infinitely many `n` with two consecutive prime gaps larger than `pₙ / n ∼ log n`. Ford, Maynard,
and Tao [FMT18] proved that for every fixed `k` there are infinitely many `n` with `k` consecutive
prime gaps all of size `≫ log pₙ · log log pₙ · log log log log pₙ / log log log pₙ`.
-/
@[category research solved, AMS 11]
theorem erdos_968.variants.infinite_increasingTriples :
    answer(True) ↔ {n : ℕ | u n < u (n + 1) ∧ u (n + 1) < u (n + 2)}.Infinite := by
  sorry

/--
Erdős asked whether there are infinitely many solutions to `uₙ > uₙ₊₁ > uₙ₊₂`.

The answer is yes. Since `uₙ > uₙ₊₁` is equivalent to `pₙ₊₁ - pₙ < pₙ / n`, it suffices to have
infinitely many `n` with `pₙ₊₂ - pₙ` bounded, because `pₙ / n → ∞`. Maynard [Ma15] proved that
`liminf (pₙ₊₂ - pₙ) < ∞`.
-/
@[category research solved, AMS 11]
theorem erdos_968.variants.infinite_decreasingTriples :
    answer(True) ↔ {n : ℕ | u n > u (n + 1) ∧ u (n + 1) > u (n + 2)}.Infinite := by
  sorry

end Erdos968
