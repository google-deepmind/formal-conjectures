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
# Erdős Problem 1088

*Reference:* [erdosproblems.com/1088](https://www.erdosproblems.com/1088)
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos1088

variable {d : ℕ}

/-- A finite set of points has all pairwise distances distinct. -/
def PairwiseDistancesDistinct (A : Finset (ℝ^d)) : Prop :=
  distinctDistances A = Nat.choose A.card 2

/-- The finite set `S` contains an `n`-point subset with all pairwise distances distinct. -/
def HasSubsetWithDistinctDistances (n : ℕ) (S : Finset (ℝ^d)) : Prop :=
  ∃ A : Finset (ℝ^d), A ⊆ S ∧ A.card = n ∧ PairwiseDistancesDistinct A

/--
The set of cardinalities `m` such that every `m`-point subset of `ℝ^d` contains an `n`-point
subset with all pairwise distances distinct.
-/
def cardSet (d n : ℕ) : Set ℕ :=
  { m | n ≤ m ∧ ∀ S : Finset (ℝ^d), S.card = m → HasSubsetWithDistinctDistances n S }

/--
The least `m` such that every `m`-point subset of `ℝ^d` contains an `n`-point subset with all
pairwise distances distinct.
-/
noncomputable def f (d n : ℕ) : ℕ := sInf (cardSet d n)

/-- `f d n` is the least cardinality with the required distinct-distance property. -/
@[category API, AMS 51]
theorem f_isLeast (d n : ℕ) : IsLeast (cardSet d n) (f d n) := by
  sorry

/--
Let $f_d(n)$ be the minimal $m$ such that any set of $m$ points in $\mathbb{R}^d$ contains a set of
$n$ points for which any two determined distances are distinct. Erdős Problem 1088 asks to
estimate $f_d(n)$. In particular, is it true that, for every fixed $n \geq 3$,
$$
f_d(n) = 2^{o(d)}
$$
as $d \to \infty$?

The little-$o$ condition is stated after taking the base-$2$ logarithm.
-/
@[category research open, AMS 51]
theorem erdos_1088 :
    answer(sorry) ↔
      ∀ n ≥ 3,
        (fun d : ℕ ↦ Real.logb 2 (f d n : ℝ)) =o[atTop] (fun d : ℕ ↦ (d : ℝ)) := by
  sorry

end Erdos1088
