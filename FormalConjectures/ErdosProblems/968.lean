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
# Erdős Problem 968

Let `uₙ = pₙ / n`, where `pₙ` is the `n`th prime. Does the set of `n` such that `uₙ < uₙ₊₁`
have positive density?

Erdős and Prachar also proved that `∑_{pₙ < x} |uₙ₊₁ - uₙ| ≍ (log x)^2`, and that the set of `n`
such that `uₙ > uₙ₊₁` has positive density. Erdős also asked whether there are infinitely many
increasing triples `uₙ < uₙ₊₁ < uₙ₊₂` or decreasing triples `uₙ > uₙ₊₁ > uₙ₊₂`.

*Reference:* [erdosproblems.com/968](https://www.erdosproblems.com/968)

[ErPr61] Erdős, P. and Prachar, K., _Sätze und Probleme über pₖ/k_. Abh. Math. Sem. Univ. Hamburg
(1961/62), 251–256.
-/

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
Does the set `{n | u n < u (n+1)}` have positive natural density?
-/
@[category research open, AMS 11]
theorem erdos_968 : answer(sorry) ↔ {n : ℕ | u n < u (n + 1)}.HasPosDensity := by
  sorry

/--
Erdős and Prachar proved `∑_{pₙ < x} |u (n+1) - u n| ≍ (log x)^2` (see [ErPr61]).

We encode `∑_{pₙ < x}` as a sum over `n < Nat.primeCounting' x` (the number of primes `< x`).
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/968.lean", AMS 11]
theorem erdos_968.variants.sum_abs_diff_isTheta_log_sq :
    (fun x : ℕ =>
        ∑ n < Nat.primeCounting' x, |u (n + 1) - u n|) =Θ[atTop]
      fun x : ℕ => log x ^ 2 := by
  sorry

/--
Erdős and Prachar proved that the set `{n | u n > u (n+1)}` has positive natural density
(see [ErPr61]).
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/968.lean", AMS 11]
theorem erdos_968.variants.decreasingSteps_hasPosDensity :
    {n : ℕ | u n > u (n + 1)}.HasPosDensity := by
  sorry

/--
Erdős asked whether there are infinitely many solutions to `uₙ < uₙ₊₁ < uₙ₊₂`.
-/
@[category research open, AMS 11]
theorem erdos_968.variants.infinite_increasingTriples :
    answer(sorry) ↔ {n : ℕ | u n < u (n + 1) ∧ u (n + 1) < u (n + 2)}.Infinite := by
  sorry

/--
Erdős asked whether there are infinitely many solutions to `uₙ > uₙ₊₁ > uₙ₊₂`.
-/
@[category research open, AMS 11]
theorem erdos_968.variants.infinite_decreasingTriples :
    answer(sorry) ↔ {n : ℕ | u n > u (n + 1) ∧ u (n + 1) > u (n + 2)}.Infinite := by
  sorry

end Erdos968
