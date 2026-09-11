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
# A density-one sign pattern for the prime-step Farey L² discrepancy

*Reference:* S. Shai, *The per-step Farey discrepancy* (2026),
https://github.com/SaarShai/Primes-Equispaced .
AI disclosure: conjecture studied with assistance from Claude (Anthropic).

Let `fareySet N` be the order-`N` Farey fractions in `(0, 1]` and let
`fareyL2Discrepancy N = ∫₀¹ (#{f ∈ fareySet N : f ≤ x} − |fareySet N|·x)² dx`
be the `L²` (Weyl) discrepancy. For a prime `p` the prime-step increment is
`primeStepIncrement p = fareyL2Discrepancy (p-1) − fareyL2Discrepancy p`,
the change when the `p−1` new fractions `{k/p}` are inserted, and
`mertens n = ∑_{k ≤ n} μ k`.

The *pointwise* relation `sgn (primeStepIncrement p) = sgn (− mertens p)`
for every prime `p` with `mertens p ≤ −3` is **false** (e.g. it fails at
`p = 243799`). The conjecture below is the surviving **density-one** form:
numerically about `73 %` of qualifying primes up to `10⁷` satisfy it, and it
is expected to hold with density one under the `L`-function hypotheses that
control the explicit-formula expansion of `primeStepIncrement` (a
Chebyshev-bias statement in the spirit of Rubinstein–Sarnak, 1994). It is
open.
-/

open scoped BigOperators Classical
open Finset MeasureTheory

namespace FareyDiscrepancySignPattern

/-- The order-`N` Farey fractions: reduced `p/q ∈ (0,1]` with `1 ≤ q ≤ N`,
`1 ≤ p ≤ q`, `Nat.Coprime p q`, as a `Finset ℚ`. -/
noncomputable def fareySet (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).biUnion fun q =>
    ((Finset.Icc 1 q).filter fun p => Nat.Coprime p q).image
      fun p => (p : ℚ) / (q : ℚ)

/-- The Farey counting function `#{ f ∈ fareySet N : (f : ℝ) ≤ x }`. -/
noncomputable def fareyCount (N : ℕ) (x : ℝ) : ℕ :=
  ((fareySet N).filter fun f => (f : ℝ) ≤ x).card

/-- The signed Farey discrepancy `D_N(x) = #{f ≤ x} − |F_N|·x`. -/
noncomputable def fareyDiscrepancy (N : ℕ) (x : ℝ) : ℝ :=
  (fareyCount N x : ℝ) - ((fareySet N).card : ℝ) * x

/-- The `L²` (Weyl) discrepancy `W N = ∫₀¹ D_N(x)² dx`. -/
noncomputable def fareyL2Discrepancy (N : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, (fareyDiscrepancy N x) ^ 2

/-- The prime-step increment `ΔW p = W (p-1) − W p`. -/
noncomputable def primeStepIncrement (p : ℕ) : ℝ :=
  fareyL2Discrepancy (p - 1) - fareyL2Discrepancy p

/-- The Mertens function `M n = ∑_{k ≤ n} μ k`. -/
noncomputable def mertens (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.moebius k

/-- Real sign, with `sgn 0 = 0`. -/
noncomputable def signReal (x : ℝ) : ℤ :=
  if x > 0 then 1 else if x < 0 then -1 else 0

/-- Integer sign, with `sgn 0 = 0`. -/
def signInt (n : ℤ) : ℤ := if n > 0 then 1 else if n < 0 then -1 else 0

/-- The prime `p` *agrees* if `sgn (ΔW p) = sgn (− M p)`. -/
noncomputable def agreesAtPrime (p : ℕ) : Prop :=
  signReal (primeStepIncrement p) = signInt (- mertens p)

/-- Among the primes `p` with `mertens p ≤ −3`, the proportion that satisfy
`sgn (primeStepIncrement p) = sgn (− mertens p)` tends to `1`: for every
`ε > 0` there is `X₀` such that for all `X ≥ X₀`, whenever at least one such
prime is `≤ X`, the agreeing fraction is `≥ 1 − ε`. (The pointwise form,
`ε = 0`, is false; this density-one form is the open conjecture.) -/
@[category research open, AMS 11]
theorem farey_discrepancy_density_one_sign :
    ∀ ε > (0 : ℝ), ∃ X₀ : ℕ, ∀ X ≥ X₀,
      let qualifying : ℝ :=
        (((Finset.range (X + 1)).filter
          (fun p => Nat.Prime p ∧ mertens p ≤ -3)).card : ℝ)
      let agreeing : ℝ :=
        (((Finset.range (X + 1)).filter
          (fun p => Nat.Prime p ∧ mertens p ≤ -3 ∧ agreesAtPrime p)).card : ℝ)
      0 < qualifying → 1 - ε ≤ agreeing / qualifying := by
  sorry

end FareyDiscrepancySignPattern
