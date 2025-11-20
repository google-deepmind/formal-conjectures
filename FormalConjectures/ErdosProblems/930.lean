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
# Erdős Problem 930

*Reference:* [erdosproblems.com/930](https://www.erdosproblems.com/930)
-/

open Finset Nat

namespace Erdos930

/--
$n$ is a perfect power if there exist natural numbers $m$ and $l$
such that $1 < m$, $1 < l$, and $m^l = n$.
-/
def PerfectPower (n : ℕ) : Prop :=
  ∃ m l, 1 < m ∧ 1 < l ∧ m^l = n

/--
Is it true that, for every $r$, there is a $k$ such that
if $I_1,\ldots,I_r$ are disjoint intervals of consecutive integers,
all of length at least $k$, then
$$
  \prod_{1\leq i\leq r}\prod_{m\in I_i}m
$$
is not a perfect power?
-/
@[category research open, AMS 11]
theorem erdos_930 :
  ∀ r, ∃ k, ∀ (I : Fin r → Finset ℕ),
    (∀ i j : Fin r, i ≠ j → Disjoint (I i) (I j)) →
      (∀ i : Fin r, k ≤ (I i).card ∧ ∃ a, I i = Ico a (a + (I i).card)) →
        ¬ PerfectPower (∏ i : Fin r, ∏ m ∈ I i, m) := by
  sorry

end Erdos930
