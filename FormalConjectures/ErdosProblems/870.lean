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

import FormalConjecturesUtil

/-!
# Erdős Problem 870

*Reference:* [erdosproblems.com/870](https://www.erdosproblems.com/870)
-/

open Filter Set

namespace Erdos870

/--
An asymptotic additive basis of order `h` is minimal when removing any element leaves infinitely
many integers not representable as a sum of `h` elements.
-/
def MinAsymptoticAddBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticAddBasisOfOrder A h ∧ ∀ n ∈ A, ¬ IsAsymptoticAddBasisOfOrder (A \ {n}) h

/--
`r A k n` counts representations of `n` as a sum of at most `k` elements of `A`
(ordered tuples). The threshold `r(n) ≥ c log n` is unaffected up to the choice of `c`.
-/
noncomputable def r (A : Set ℕ) (k n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k,
    (({p : Fin m → ℕ | (∀ i, p i ∈ A) ∧ ∑ i, p i = n} : Set (Fin m → ℕ)).encard : ℝ)

/--
Let $k\geq 3$ and $A$ be an additive basis of order $k$. Does there exist a constant $c=c(k)>0$
such that if $r(n)\geq c\log n$ for all large $n$ then $A$ must contain a minimal basis of
order $k$? (Here $r(n)$ counts the number of representations of $n$ as the sum of at most $k$
elements from $A$.)
-/
@[category research open, AMS 5 11]
theorem erdos_870 : answer(sorry) ↔
    ∀ k ≥ 3, ∃ c > (0 : ℝ), ∀ (A : Set ℕ),
      IsAsymptoticAddBasisOfOrder A k →
      (∀ᶠ n : ℕ in atTop, c * Real.log n ≤ r A k n) →
      ∃ B ⊆ A, MinAsymptoticAddBasisOfOrder B k := by
  sorry

end Erdos870
