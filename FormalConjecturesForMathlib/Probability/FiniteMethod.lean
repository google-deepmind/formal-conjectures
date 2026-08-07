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

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The finite probabilistic method (averaging / pigeonhole primitive)

This file provides the core averaging lemma underlying the elementary form of Erdős's
**probabilistic method**:

> If the sum of a `ℕ`-valued function `f` over a finite set `s` is strictly less than the
> cardinality of `s`, then `f` vanishes somewhere on `s`.

Interpreting `f a` as "the number of bad configurations caused by choice `a`", and sampling
`a` uniformly from `s`, the expected number of bad configurations is `(∑ f) / |s| < 1`,
so there must exist at least one `a ∈ s` with `f a = 0`.

This is used by:
- `FormalConjectures/Probabilistic/RamseyDiagonalLowerBound.lean`
  to close the `R(k,k) > 2^{k/2}` lower bound (Erdős 1947).
- downstream deletion-method / alteration-method arguments.

Both the `ℕ`-form and a convenience `ℝ`-form are provided; the latter is useful when the
expectation bound is derived via `rpow`/`log` manipulations on the reals and only later
cast back to counting.

## References

- [Er47] Erdős, P. (1947). "Some remarks on the theory of graphs." *Bull. Amer. Math. Soc.*
  53, pp. 292--294.
- [AlSp16] Alon, N. and Spencer, J. (2016). *The Probabilistic Method* (4th ed.), §1.1.
-/

namespace FormalConjecturesForMathlib.Probability

open Finset

/-- **Finite probabilistic method (integer form).**

If `∑ x ∈ s, f x < s.card`, then there exists `a ∈ s` with `f a = 0`.

**Proof idea.** Contrapositive: if every value is at least `1`, the sum is at least
`s.card · 1 = s.card`, contradicting the hypothesis. -/
theorem Finset.exists_eq_zero_of_sum_lt_card
    {α : Type*} {s : Finset α} {f : α → ℕ} (h : ∑ x ∈ s, f x < s.card) :
    ∃ a ∈ s, f a = 0 := by
  by_contra hne
  push_neg at hne
  have hge : ∀ a ∈ s, 1 ≤ f a :=
    fun a ha => Nat.one_le_iff_ne_zero.mpr (hne a ha)
  have hbound : s.card ≤ ∑ x ∈ s, f x := by
    calc s.card
        = ∑ _x ∈ s, 1 := by rw [sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ x ∈ s, f x := sum_le_sum hge
  omega

/-- **Finite probabilistic method (real form).**

If `(∑ x ∈ s, (f x : ℝ)) < s.card`, then there exists `a ∈ s` with `f a = 0`.

This is the same statement as `Finset.exists_eq_zero_of_sum_lt_card` after casting the
counting inequality to `ℝ`; it is the convenient entry point when `f` arises as an expectation
whose bound was computed in the reals (e.g. via `Real.rpow` / `Real.log`). -/
theorem Finset.exists_eq_zero_of_real_sum_lt_card
    {α : Type*} {s : Finset α} {f : α → ℕ}
    (h : (∑ x ∈ s, (f x : ℝ)) < s.card) : ∃ a ∈ s, f a = 0 := by
  apply Finset.exists_eq_zero_of_sum_lt_card
  have hcast : ((∑ x ∈ s, f x : ℕ) : ℝ) = ∑ x ∈ s, (f x : ℝ) :=
    Nat.cast_sum s f
  have : ((∑ x ∈ s, f x : ℕ) : ℝ) < (s.card : ℝ) := hcast ▸ h
  exact_mod_cast this

end FormalConjecturesForMathlib.Probability
