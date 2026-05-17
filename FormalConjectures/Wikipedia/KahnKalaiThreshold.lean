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
# The Kahn–Kalai threshold conjecture (Kahn–Kalai 2007, proved Park–Pham 2022)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Kahn%E2%80%93Kalai_conjecture)
* [KK07] Kahn, J. and Kalai, G. (2007). "Thresholds and expectation thresholds."
  *Combin. Probab. Comput.* 16, pp. 495--502.
* [PP24] Park, J. and Pham, H.T. (2024). "A proof of the Kahn–Kalai conjecture." *J. Amer.
  Math. Soc.* 37, pp. 235--243.
-/

open Classical Finset

namespace KahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

/- ## Monotone families

A family `F ⊆ 2^X` is **monotone (increasing)** if it is upward-closed: whenever `A ∈ F` and
`A ⊆ B ⊆ X` then `B ∈ F`. We work with `F : Set (Finset X)` so that `F` is a subset of the
powerset `2^X` represented as `Finset X`. -/

/-- A family of finite subsets of `X` is **monotone increasing** if it is closed under taking
supersets (equivalently, upward-closed in the inclusion order on `Finset X`). -/
def IsMonotoneFamily (F : Set (Finset X)) : Prop :=
  ∀ ⦃A B : Finset X⦄, A ∈ F → A ⊆ B → B ∈ F

/- ## p-random subsets

For `p ∈ [0, 1]`, the `p`-random subset of `X` (aka `X_p`) is obtained by independently
including each `x ∈ X` with probability `p`. The probability that the resulting subset lies in
`F` is
  `μ_p(F) := ∑_{A ⊆ X} p^|A| · (1-p)^(|X|-|A|) · [A ∈ F]`
i.e. the probability of `F` under the `Bernoulli(p)` product measure on `2^X`. -/

/-- The **`p`-measure of a family** `F` on a finite ground set `X`: the probability that a
`p`-random subset of `X` lies in `F`, computed as an explicit sum over `Finset X` rather than
as a measure-theoretic integral. -/
noncomputable def familyMeasure (F : Set (Finset X)) (p : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset X).powerset,
    (if A ∈ F then (1 : ℝ) else 0) *
      p ^ A.card * (1 - p) ^ (Fintype.card X - A.card)

/-- The **probability threshold** `p_c(F)` of a monotone family `F`: the infimum of `p ∈ [0,1]`
such that `familyMeasure F p ≥ 1/2`.

For a non-empty monotone family this set is non-empty (it contains `p = 1`, at which the
measure is the indicator that `Finset.univ ∈ F`, which is `1` by monotonicity when `F` is
non-empty), and a bounded-below subset of the reals has an infimum. -/
noncomputable def probabilityThreshold (F : Set (Finset X)) : ℝ :=
  sInf { p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ familyMeasure F p ≥ 1 / 2 }

/- ## Expectation thresholds

The **expectation threshold** `q_c(F)` is the infimum of `q ∈ [0, 1]` such that the expected
number of *minimal* elements of `F` contained in a `q`-random subset is at least `1/2`. We
formalise minimality inside `F` and the expected-minimal-count sum explicitly. -/

/-- A set `A ∈ F` is a **minimal element of `F`** if no proper subset of `A` lies in `F`. For
monotone-increasing `F`, the minimal elements generate `F` by upward closure. -/
def IsMinimalIn (F : Set (Finset X)) (A : Finset X) : Prop :=
  A ∈ F ∧ ∀ B ∈ F, B ⊆ A → B = A

/-- Under the `q`-random model on `X`, the **expected number of minimal `F`-elements** that
happen to lie inside the random subset equals
  `∑_{A minimal in F} q^|A|`.
(Each minimal `A` is contained in a `q`-random subset with probability exactly `q^|A|`,
independently over the `|A|` mandatory vertices; sum of indicator expectations over a finite
set is the finite sum.) -/
noncomputable def expectedMinimalCount (F : Set (Finset X)) (q : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset X).powerset.filter (fun A => IsMinimalIn F A),
    q ^ A.card

/-- The **expectation threshold** `q_c(F)`: the infimum of `q ∈ [0,1]` such that the expected
number of minimal `F`-elements fitting inside a `q`-random subset is at least `1/2`. -/
noncomputable def expectationThreshold (F : Set (Finset X)) : ℝ :=
  sInf { q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ expectedMinimalCount F q ≥ 1 / 2 }

/- ## The Kahn–Kalai inequality (Park–Pham 2022) -/

/--
**Kahn–Kalai threshold inequality** (Kahn–Kalai 2007 conjecture; Park–Pham 2022 proof).

There exists a universal constant `C > 0` such that for every finite ground set `X` and every
non-empty monotone increasing family `F ⊆ 2^X`,
  `p_c(F) ≤ C · q_c(F) · log(|X| + 2)`.

**Status:** PROVED (Park–Pham 2022; published in *J. Amer. Math. Soc.* 2024).

**Proof sketch.** The Park–Pham argument is a short (≈ 6 pages) covering argument: given a
cover of `F` by "small" sets in a sense measured by `q_c`, one constructs a bounded-size
sunflower-free system witnessing the probability-threshold bound up to a `log |X|` factor.
Formalising this requires a careful account of covers, minimum-weight sunflower covers, and
several discrete entropy / `union-bound` estimates that are not yet in Mathlib. We leave the
proof as `sorry`.

The informal conjecture `p_c ≤ C · q_c · log(|X|+2)` is sharp up to the constant `C`
(matching the "shifted coupon collector" lower bound on `p_c / q_c`); see [KK07, §3].
-/
@[category research solved, AMS 5]
theorem kahn_kalai :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      (F : Set (Finset X)),
      F.Nonempty → IsMonotoneFamily F →
      probabilityThreshold F ≤
        C * expectationThreshold F * Real.log ((Fintype.card X : ℝ) + 2) := by
  -- Park–Pham 2022 [PP24]. Deferred pending Mathlib sunflower / covering helpers.
  sorry

/- ## Easy consequences and sanity checks -/

/--
**Monotonicity of `familyMeasure`** (sanity check): increasing the sampling probability `p`
weakly increases the probability of landing in a monotone family.

We state this as the expected Kahn–Kalai-style "threshold exists" side condition, proof
deferred; the fact is standard but the elementary proof (FKG inequality / direct coupling)
requires writing out a product-measure coupling which we skip here.
-/
@[category research solved, AMS 5]
theorem familyMeasure_mono (F : Set (Finset X)) (_hMono : IsMonotoneFamily F)
    {p q : ℝ} (_hp : 0 ≤ p) (_hpq : p ≤ q) (_hq : q ≤ 1) :
    familyMeasure F p ≤ familyMeasure F q := by
  -- Standard FKG/coupling. Deferred.
  sorry

/--
**Trivial lower bound `q_c ≤ p_c`** (one direction of the Kahn–Kalai inequality; the hard
direction is the `log |X|`-factor upper bound on `p_c`).

If `F` is non-empty and monotone increasing, then `expectationThreshold F ≤
probabilityThreshold F`: the expected number of minimal `F`-elements in a `q`-random subset
is a lower bound for the probability that the subset lies in `F` (`Markov's inequality`
plus monotonicity), so any `p` with `μ_p(F) ≥ 1/2` has expected minimal count `≥ 1/2` too.

Formalisation deferred: the Markov step is short but requires wiring up `expectedMinimalCount`
to `familyMeasure`.
-/
@[category research solved, AMS 5]
theorem expectationThreshold_le_probabilityThreshold
    (F : Set (Finset X)) (_hne : F.Nonempty) (_hMono : IsMonotoneFamily F) :
    expectationThreshold F ≤ probabilityThreshold F := by
  -- Markov inequality; deferred.
  sorry

end KahnKalai
