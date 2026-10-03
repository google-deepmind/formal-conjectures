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

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Normal numbers

A real number $x$ is *simply normal in base* $b$ if every digit
$d \in \{0,1,\dots,b-1\}$ appears with asymptotic frequency $1/b$
in the base-$b$ expansion of $x$. It is *normal in base* $b$ if, for every
$k \ge 1$, every string of $k$ digits appears with asymptotic frequency $1/b^k$.

A number that is normal in every integer base $b \ge 2$
is called *absolutely normal*.

Despite extensive empirical evidence, it remains unknown whether
classical constants such as $\pi$, $e$, or $\sqrt{2}$ are normal in any base.

*References*:
- [Wikipedia, Normal number](https://en.wikipedia.org/wiki/Normal_number)
- [Wikipedia, Borel normal number](https://en.wikipedia.org/wiki/Borel_normal_number)

## Main definitions

* `digitSeq`: the sequence of digits in the base-`b` fractional expansion of a real number.
* `IsSimplyNormalInBase`: a real number is simply normal in base `b`.
* `IsNormalInBase`: a real number is normal in base `b`.
* `IsAbsolutelyNormal`: a real number is normal in every base `b ≥ 2`.
-/

@[expose] public section

open Real Filter

namespace NormalNumber

/-- The `n`-th digit (0-indexed) after the radix point in the base-`b`
expansion of `x`.

Concretely,
`digitSeq b x n = ⌊b^(n+1) * {x}⌋ mod b`,
where `{x}` denotes the fractional part of `x`. -/
noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

/-- A real number `x` is *simply normal in base* `b`
if every digit `d < b` appears with asymptotic frequency `1 / b`
in the base-`b` fractional expansion of `x`. -/
noncomputable def IsSimplyNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ d : ℕ, d < b →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun k => digitSeq b x k = d)).card : ℝ) / n)
      atTop
      (nhds (1 / (b : ℝ)))

/-- If the fractional part of `x` is `0`, then every digit of `x` is `0`. -/
theorem digitSeq_eq_zero_of_fract_eq_zero {b : ℕ} {x : ℝ} (hx : Int.fract x = 0) (n : ℕ) :
    digitSeq b x n = 0 := by
  simp [digitSeq, hx]

/-- A real number whose fractional part is `0` is not simply normal in any base `b ≥ 2`:
all of its digits are `0`, so the digit `1` has frequency `0` instead of `1 / b`. -/
theorem not_isSimplyNormalInBase_of_fract_eq_zero {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : Int.fract x = 0) : ¬ IsSimplyNormalInBase b x := by
  intro h
  have hfil : ∀ n : ℕ, ((Finset.range n).filter fun k => digitSeq b x k = 1) = ∅ := fun n => by
    simp [digitSeq_eq_zero_of_fract_eq_zero hx]
  have key := h 1 (by omega)
  simp only [hfil, Finset.card_empty, Nat.cast_zero, zero_div] at key
  have hzero : (1 : ℝ) / b = 0 := tendsto_nhds_unique key tendsto_const_nhds
  rw [div_eq_zero_iff, Nat.cast_eq_zero] at hzero
  rcases hzero with hzero | hzero
  · exact one_ne_zero hzero
  · omega

/-- A real number `x` is *normal in base* `b`
if every string `w` of `k` digits `< b` appears with asymptotic frequency `1 / b ^ k`
in the base-`b` fractional expansion of `x`, that is, the proportion of positions `i < n`
at which `w` occurs tends to `1 / b ^ k`. -/
noncomputable def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℕ), (∀ j, w j < b) →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun i => ∀ j : Fin k, digitSeq b x (i + j) = w j)).card : ℝ) / n)
      atTop
      (nhds (1 / (b : ℝ) ^ k))

/-- A number that is normal in base `b` is simply normal in base `b`. -/
theorem IsNormalInBase.isSimplyNormalInBase {b : ℕ} {x : ℝ} (h : IsNormalInBase b x) :
    IsSimplyNormalInBase b x := by
  intro d hd
  simpa [Fin.forall_fin_one] using h 1 (fun _ => d) (fun _ => hd)

/-- A real number `x` is *absolutely normal*
if it is normal in every integer base `b ≥ 2`. -/
noncomputable def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalInBase b x

end NormalNumber
