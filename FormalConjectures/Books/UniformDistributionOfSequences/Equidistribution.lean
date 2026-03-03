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

import FormalConjectures.Util.ProblemImports
/-!
# Equidistributed Sequences

Corollary 4.2 of Chapter 1 states that the sequence $(x^n), n = 1, 2, ... ,$ is equidistributed modulo 1 for
almost all x > 1. And a little bit further down:
"one does not know whether sequences such as $(e^n)$, $(π^n)$, or even $((\frac 3 2)^n)$"
are equidistributed modulo 1 or not.

*References:*
  - [Uniform Distribution of Sequences](https://store.doverpublications.com/products/9780486149998)
by *L. Kuipers* and *H. Niederreiter*, 1974
  - [Wikipedia](https://en.wikipedia.org/wiki/Equidistributed_sequence)
-/

namespace Equidistribution

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

/--
A point `x` is an accumulation point of a sequence `s_0, s_1, ...`
if any neighbourhood of `x` contains a point of the sequence distinct
from `x`.
-/
def IsAccumulationPoint (x : ℝ) (s : ℕ → ℝ) : Prop :=
  x ∈ closure (Set.range s \ {x})

/--
If a point `x` is an accumulation point of a sequence `s_0, s_1, ...` then
there is a subsequence of `s` that tends to `x`
-/
def isAccumulationPoint_iff_exists_subsequence_tendsto
    (x : ℝ) (s : ℕ → ℝ) (hx : IsAccumulationPoint x s) :
    ∃ (u : ℕ → ℕ), StrictMono u ∧ Filter.atTop.Tendsto (s ∘ u) (𝓝 x) := by
  sorry

/--
The sequence `(3/2)^n` is equidistributed modulo `1`.
-/
@[category research open, AMS 11]
theorem isEquidistributedModuloOne_three_halves_pow :
    IsEquidistributedModuloOne (fun n => (3 / 2 : ℝ)^n) := by
  sorry

/--
The sequence `(3/2)^n` has infinitely many accumulation points modulo `1`.
-/
@[category research formally solved using formal_conjectures at "https://en.wikipedia.org/wiki/Equidistributed_sequence", AMS 11]
theorem isAccumulationPoint_three_halves_pow_infinite :
    {x | IsAccumulationPoint x (fun n => Int.fract <| (3 / 2 : ℝ)^n)}.Infinite := by
  sorry

/--
Find an accumulation point of the sequence `(3/2)^n` modulo `1`.
-/
@[category research open, AMS 11]
theorem isAccumulationPoint_three_halves_pow :
    IsAccumulationPoint answer(sorry) (fun n => Int.fract <| (3 / 2 : ℝ)^n) := by
  sorry

/--
There is an accumulation point of the sequence `(3/2)^n` modulo `1`.
-/
@[category test, AMS 11]
theorem isAccumulationPoint_three_halves_pow_exists :
    ∃ p, (IsAccumulationPoint p (fun n => Int.fract <| (3 / 2 : ℝ)^n)) := by
  sorry

end Equidistribution
