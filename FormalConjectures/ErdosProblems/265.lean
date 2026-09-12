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

import FormalConjecturesUtil

/-!
# Erdős Problem 265

*Reference:* [erdosproblems.com/265](https://www.erdosproblems.com/265)

Let $1 \leq a_1 < a_2 < \cdots$ be an increasing sequence of integers. How fast can
$a_n \to \infty$ grow if $\sum \frac{1}{a_n}$ and $\sum \frac{1}{a_n - 1}$ are both
rational?

Two points of care in this formalisation.

*The literal statement admits $a_1 = 1$*, which makes $a_1 - 1 = 0$ and the second
series ill-defined. We therefore require $2 \leq a_0$; combined with `StrictMono` this
gives $2 \leq a_n$ for all $n$. Cantor's example correspondingly begins at $n = 3$.
This ambiguity has been reported upstream at
[teorth/erdosproblems#359](https://github.com/teorth/erdosproblems/issues/359).

*The growth condition is deliberately not stated as* $1 < \limsup a_n^{1/2^n}$ over
$\mathbb{R}$. `Filter.limsup` unfolds to `sInf {b | ∀ᶠ n, f n ≤ b}`, and
`Real.sInf_empty : sInf ∅ = 0`, so an unbounded sequence yields the junk value $0$ and
the inequality would evaluate to `False` precisely for the fastest-growing sequences —
inverting the intended meaning. We use the equivalent existential form with `∃ᶠ`
(frequently): $\limsup > 1$ is an infinitely-often condition, so `∀ᶠ` would encode the
strictly stronger $\liminf > 1$.
-/

open Filter

open scoped Topology

namespace Erdos265

/--
A strictly increasing sequence $a$ of integers with $2 \leq a_0$, such that both
$\sum \frac{1}{a_n}$ and $\sum \frac{1}{a_n - 1}$ converge to rational numbers.
-/
def IsRationalPairSequence (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
    2 ≤ a 0 ∧
    (∃ q : ℚ, ∑' n, (1 : ℝ) / (a n : ℝ) = q) ∧
    (∃ q : ℚ, ∑' n, (1 : ℝ) / ((a n : ℝ) - 1) = q)

/--
$2 \leq a_0$ together with `StrictMono` already forces $2 \leq a_n$ everywhere, so
taking the minimal hypothesis in `IsRationalPairSequence` loses nothing.
-/
@[category API, AMS 11]
theorem two_le_of_isRationalPairSequence {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    ∀ n, 2 ≤ a n :=
  fun n => le_trans ha.2.1 (ha.1.monotone (Nat.zero_le n))

/--
Cantor's example. The source page states it as $a_n = \binom{n}{2}$; we index from
$n = 3$, i.e. $a_n = \binom{n+3}{2} = 3, 6, 10, \ldots$, because $\binom{2}{2} = 1$
would make $a_n - 1 = 0$ (the ambiguity reported at teorth/erdosproblems#359).
Here $\sum \frac{1}{a_n} = 1$, and since $\binom{n}{2} - 1 = \frac{(n-2)(n+1)}{2}$ the
second series telescopes to $\sum \frac{1}{a_n - 1} = \frac{11}{9}$. Both are rational.
-/
@[category test, AMS 11]
theorem cantor_example : IsRationalPairSequence (fun n : ℕ => (n + 3).choose 2) := by
  sorry

/--
The growth condition $\limsup a_n^{1/2^n} > 1$, stated existentially to avoid the
real-valued `limsup` junk value described in the module docstring.
-/
def GrowthExceedsOne (a : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∃ᶠ n in atTop, c ^ (2 ^ n) ≤ (a n : ℝ)

/--
**Erdős Problem 265.** The precise question that remains open is whether the growth
exponent can exceed $1$.
-/
@[category research open, AMS 11]
theorem erdos_265 : answer(sorry) ↔
    ∃ a : ℕ → ℕ, IsRationalPairSequence a ∧ GrowthExceedsOne a := by
  sorry

/-- The set of achievable doubly-exponential rates $\beta$. -/
def AchievableRates : Set ℝ :=
  {β : ℝ | 1 < β ∧ ∃ a : ℕ → ℕ, IsRationalPairSequence a ∧
    Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (β ^ n : ℝ))) atTop atTop}

/--
The folklore upper bound is what makes `sSup AchievableRates` meaningful rather than a
junk value: without `BddAbove` the supremum would silently collapse to $0$, exactly as
the naive `limsup` formulation does.
-/
@[category research solved, AMS 11]
theorem achievableRates_bddAbove : BddAbove AchievableRates := by
  sorry

/--
Companion supremum formulation of "how fast can it grow", for the reading of the problem
that asks for the extremal rate rather than for a yes/no decision.
-/
@[category research open, AMS 11]
theorem erdos_265.variants.sup_rate : sSup AchievableRates = answer(sorry) := by
  sorry

/--
Erdős believed $a_n^{1/n} \to \infty$ to be possible. This follows from the doubly
exponential construction of Kovač and Tao [KoTa24] recorded below, since
$\beta^n / n \to \infty$ for any $\beta > 1$; it is a consequence of their theorem
rather than its literal statement.

[KoTa24] Kovač, V. and Tao, T., On several irrationality problems for Ahmes series.
         arXiv:2406.17593 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_265.variants.super_exponential :
    ∃ a : ℕ → ℕ, IsRationalPairSequence a ∧
      Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) atTop atTop := by
  sorry

/--
Kovač and Tao [KoTa24] proved that such a sequence can grow doubly exponentially: there
is some $\beta > 1$ with $a_n^{1/\beta^n} \to \infty$.

[KoTa24] Kovač, V. and Tao, T., On several irrationality problems for Ahmes series.
         arXiv:2406.17593 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_265.variants.kovac_tao : ∃ β : ℝ, β ∈ AchievableRates := by
  sorry

/--
The folklore result, in the form stated on the source page: $\sum \frac{1}{a_n}$ is
irrational whenever $\lim a_n^{1/2^n} = \infty$. This is what bounds the growth from
above, and why Erdős expected $a_n^{1/2^n} \to 1$ to be necessary.
-/
@[category research solved, AMS 11]
theorem erdos_265.variants.folklore_irrational (a : ℕ → ℕ) (ha : StrictMono a)
    (h₀ : 2 ≤ a 0)
    (hg : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop atTop) :
    Irrational (∑' n, (1 : ℝ) / (a n : ℝ)) := by
  sorry

/--
Consequently no sequence admissible for Problem 265 can satisfy
$a_n^{1/2^n} \to \infty$: the growth is at most doubly exponential, and only the precise
exponent remains in question. This is also what makes `AchievableRates` bounded above.
-/
@[category research solved, AMS 11]
theorem erdos_265.variants.folklore_upper_bound (a : ℕ → ℕ)
    (hg : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop atTop) :
    ¬ IsRationalPairSequence a := by
  sorry

end Erdos265
