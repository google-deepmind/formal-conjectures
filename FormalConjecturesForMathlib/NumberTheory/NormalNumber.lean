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

public import Mathlib.Data.Real.Archimedean
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section
/-!
# Normal numbers

A real number $x$ is *normal in base* $b$ if every digit
$d \in \{0,1,\dots,b-1\}$ appears with asymptotic frequency $1/b$
in the base-$b$ expansion of $x$.

A number that is normal in every integer base $b \ge 2$
is called *absolutely normal*.

Despite extensive empirical evidence, it remains unknown whether
classical constants such as $\pi$, $e$, or $\sqrt{2}$ are normal in any base.

*References*:
- [Wikipedia, Normal number](https://en.wikipedia.org/wiki/Normal_number)
- [Wikipedia, Borel normal number](https://en.wikipedia.org/wiki/Borel_normal_number)

## Main definitions

* `digitSeq`: the sequence of digits in the base-`b` fractional expansion of a real number.
* `IsNormalInBase`: a real number is normal in base `b`.
* `IsAbsolutelyNormal`: a real number is normal in every base `b ≥ 2`.
-/

open Real Filter

namespace NormalNumber

/-- The `n`-th digit (0-indexed) after the radix point in the base-`b`
expansion of `x`.

Concretely,
`digitSeq b x n = ⌊b^(n+1) * {x}⌋ mod b`,
where `{x}` denotes the fractional part of `x`. -/
noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

/-- A real number `x` is *normal in base* `b`
if every digit `d < b` appears with asymptotic frequency `1 / b`
in the base-`b` fractional expansion of `x`. -/
noncomputable def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ d : ℕ, d < b →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun k => digitSeq b x k = d)).card : ℝ) / n)
      atTop
      (nhds (1 / (b : ℝ)))

/-- A real number `x` is *absolutely normal*
if it is normal in every integer base `b ≥ 2`. -/
noncomputable def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalInBase b x

end NormalNumber
