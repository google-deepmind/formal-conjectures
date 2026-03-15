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
# Erdős Problem 117

*Reference:* [erdosproblems.com/117](https://www.erdosproblems.com/117)

Let $h(n)$ be the least $k$ such that every group where each subset of more than $n$ elements
contains two distinct commuting elements can be covered by $k$ abelian subgroups. Pyber proved
$c_1^n < h(n) < c_2^n$ for constants $c_2 > c_1 > 1$.

[Er90] Erdős, P., *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
467-478.

[Er97f] Erdős, P., *Some unsolved problems*. Combinatorics, geometry and probability
(Cambridge, 1993) (1997), 1-10.

[Va99,5.75] Varopoulos, N. (1999), Problem 5.75.

[Py87] Pyber, L., *The number of pairwise noncommuting elements and the index of the centre in
a finite group*. J. London Math. Soc. (2) 35 (1987), 287-295.

See also: Erdős Problem 1098 (non-commuting graph formulation).
-/

namespace Erdos117

/-- A group $G$ satisfies the $n$-commuting property if every finite subset of size
greater than $n$ contains two distinct elements $x \neq y$ with $xy = yx$. -/
def HasNCommutingProperty (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (S : Finset G), n < S.card →
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ Commute x y

/-- A group $G$ can be covered by at most $k$ Abelian subgroups: there exist $k$ subgroups
$H_0, \ldots, H_{k-1}$ (possibly with repetition), each of which is abelian, whose union
is all of $G$. -/
def CoveredByAbelianSubgroups (k : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (H : Fin k → Subgroup G),
    (∀ i, IsMulCommutative (H i)) ∧
    ∀ g : G, ∃ i, g ∈ H i

/-- $h(n)$ is the least $k$ such that every group satisfying the $n$-commuting property
can be covered by at most $k$ Abelian subgroups. -/
noncomputable def erdosH (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type) [Group G],
    HasNCommutingProperty n G → CoveredByAbelianSubgroups k G}

/--
Erdős Problem 117 [Er90, Er97f, Va99]:

Let $h(n)$ be minimal such that any group $G$ satisfying the property that every
subset of more than $n$ elements contains distinct commuting elements $x \neq y$
($xy = yx$) can be covered by at most $h(n)$ Abelian subgroups.

Estimate $h(n)$ as well as possible.

Pyber [Py87] proved there exist constants $c_2 > c_1 > 1$ such that
$$c_1^n < h(n) < c_2^n.$$
The lower bound $c_1^n < h(n)$ was already known to Isaacs [Er97f].
The precise exponential growth rate of $h(n)$ remains open.
-/
@[category research solved, AMS 20]
theorem erdos_117 :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
    ∀ n : ℕ, 1 ≤ n →
      c₁ ^ n < (erdosH n : ℝ) ∧ (erdosH n : ℝ) < c₂ ^ n := by
  sorry

end Erdos117
