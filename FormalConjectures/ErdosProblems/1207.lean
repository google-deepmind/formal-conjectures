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
# Erdős Problem 1207

*References:*
- [erdosproblems.com/1207](https://www.erdosproblems.com/1207)
- [BMP05] Brass, Peter and Moser, William and Pach, János, *Research problems in discrete geometry*.
  (2005), xii+499.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [PaTa02] Pach, János and Tardos, Gábor, *Isosceles triangles determined by a planar point set*.
  Graphs Combin. (2002), 769--779.
-/

open Filter

namespace Erdos1207

/-- A set is isosceles-free if no three distinct points in it form an isosceles triangle. -/
def IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z => ¬ IsIsosceles x y z

/--
`P d n` is the largest number such that every set of `n` points in Euclidean `d`-space has an
isosceles-free subset of at least that size.
-/
noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
    m = sSup {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin d)),
      A ⊆ S ∧ IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}}

/--
Let $P_d(n)$ be such that in any set of $n$ points in $\mathbb{R}^d$ there exist at least $P_d(n)$ many points which do not contain an isosceles triangle. Estimate $P_d(n)$ - in particular, is it true that $$P_2(n)<n^{1-c}$$ for some constant $c>0$?
-/
@[category research open, AMS 52]
theorem erdos_1207 : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c) := by
  sorry

end Erdos1207
