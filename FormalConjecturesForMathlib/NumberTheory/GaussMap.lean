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
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The Gauss map and continued fraction normality

The Gauss map $T_G(x) = 1/x \bmod 1$ shifts the continued fraction expansion of $x$ by one
partial quotient. It preserves the Gauss-Kuzmin measure, and a real number is *continued
fraction normal* if its orbit under $T_G$ equidistributes with respect to that measure.
Equivalently, every block of partial quotients occurs with the frequency given by the Gauss
measure.

*References:*
- [Sch17](https://arxiv.org/abs/1701.07979) Scheerer, Adrian-Maria. "On the continued fraction
  expansion of absolutely normal numbers." arXiv preprint arXiv:1701.07979 (2017). Equation
  (1.2) is the definition of continued fraction normality used here.
- [Wikipedia, Gauss-Kuzmin](https://en.wikipedia.org/wiki/Gauss%E2%80%93Kuzmin_distribution)

## Main definitions

* `gaussMap`: the Gauss map.
* `gaussKuzmin`: the Gauss-Kuzmin measure of an interval.
* `IsCFNormal`: a real number is continued fraction normal.
-/

@[expose] public section

open Filter

/--
The Gauss map $T_G(x) = 1/x \bmod 1$, with $T_G(0) = 0$. Iterating it on $x \in [0, 1)$ shifts
the continued fraction expansion of $x$ by one partial quotient.
-/
noncomputable def gaussMap (x : ℝ) : ℝ := Int.fract x⁻¹

/--
The Gauss-Kuzmin measure of $[\alpha, \beta)$,
$$\mu_G([\alpha, \beta)) = \frac{1}{\log 2} \int_\alpha^\beta \frac{dx}{1 + x}
  = \frac{1}{\log 2} \log \frac{1 + \beta}{1 + \alpha}.$$
-/
noncomputable def gaussKuzmin (α β : ℝ) : ℝ := Real.log ((1 + β) / (1 + α)) / Real.log 2

/--
A real number $x$ is *continued fraction normal* if for all $0 \le \alpha < \beta < 1$ the orbit
of $x$ under the Gauss map visits $[\alpha, \beta)$ with asymptotic frequency
$\mu_G([\alpha, \beta))$ [Sch17, (1.2)]. Equivalently, every block of partial quotients occurs
with the frequency given by the Gauss measure.
-/
noncomputable def IsCFNormal (x : ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α < β → β < 1 →
    Tendsto (fun n : ℕ ↦ (((Finset.range n).filter
      fun i ↦ gaussMap^[i] x ∈ Set.Ico α β).card : ℝ) / n) atTop (nhds (gaussKuzmin α β))

/-- The Gauss map fixes $0$, matching the convention $T_G(0) = 0$. -/
@[simp]
theorem gaussMap_zero : gaussMap 0 = 0 := by
  simp [gaussMap]

/-- The Gauss-Kuzmin measure of the whole interval $[0, 1)$ is $1$. -/
theorem gaussKuzmin_zero_one : gaussKuzmin 0 1 = 1 := by
  rw [gaussKuzmin]
  norm_num
