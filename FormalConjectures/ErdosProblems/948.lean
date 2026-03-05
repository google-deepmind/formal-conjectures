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
# Erdős Problem 948

*Reference:* [erdosproblems.com/948](https://www.erdosproblems.com/948)

Erdős initially asked whether this is possible with the set being monochromatic,
but Galvin showed that this is not always possible. This is a variant of
Hindman's theorem (see [532]).
-/

open Finset BigOperators

namespace Erdos948

/-- Is there a function $f : \mathbb{N} \to \mathbb{N}$ and $k \in \mathbb{N}$ such that for any
$k$-colouring $\chi$ of the natural numbers, there is a strictly increasing sequence $a$ with
$a(n) < f(n)$ for infinitely many $n$, and the finite subset sums of the sequence do not achieve
all $k$ colours? -/
@[category research open, AMS 5]
theorem erdos_948 : answer(sorry) ↔
    ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ (χ : ℕ → Fin k),
      ∃ (a : ℕ → ℕ), StrictMono a ∧
        Set.Infinite {n : ℕ | a n < f n} ∧
        ∃ (c : Fin k), ∀ (S : Finset ℕ), S.Nonempty →
          χ (∑ i ∈ S, a i) ≠ c := by
  sorry

end Erdos948
