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

public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

open scoped Topology

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed on
an interval `[a, b]` if for every subinterval `[c, d]` of `[a, b]` we have
`lim_{n→ ∞} |{s_1, ..., s_n} ∩ [c, d]| / n = (d - c)/(b-a)`
-/
def IsEquidistributed (a b : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ c d, c ≤ d → Set.Icc c d ⊆ Set.Icc a b →
  Filter.atTop.Tendsto (fun n => ((Finset.range n).filter
    fun m => s m ∈ Set.Icc c d).card / (n : ℝ)) (𝓝 <| (d - c) / (b - a))

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed
modulo 1 or uniformly distributed modulo 1 if the sequence of the fractional parts of
`a_n`, denoted by `(a_n)` or by `a_n − ⌊a_n⌋`, is equidistributed in the interval `[0, 1]`.
-/
def IsEquidistributedModuloOne (s : ℕ → ℝ) : Prop :=
  IsEquidistributed 0 1 (fun n => Int.fract (s n))
