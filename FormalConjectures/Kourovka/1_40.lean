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
# Conjecture 1.40

by Sh. S. Kemkhadze

Is a group a nilgroup if it is the product of two normal nilsubgroups?

Here a nilgroup (Engel group) is a group in which every element is an Engel
element. This is the Engel-group analogue of Fitting's theorem, which
guarantees that the product of two normal nilpotent subgroups is nilpotent.

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
-/

namespace Kourovka.«1.40»

variable {G : Type*} [Group G]

/-- The iterated commutator $[x,\, {}_n y]$, defined by $[x,\, {}_0 y] = x$ and
$[x,\, {}_{n+1} y] = [[x,\, {}_n y], y]$. -/
def engelCommutator (x y : G) : ℕ → G
  | 0 => x
  | n + 1 => ⁅engelCommutator x y n, y⁆

/-- An element $y$ of a group $G$ is a (left) Engel element if for every
$x \in G$ there is some $n$ with $[x,\, {}_n y] = 1$. -/
def IsEngelElement (y : G) : Prop :=
  ∀ x : G, ∃ n : ℕ, engelCommutator x y n = 1

/-- A nilgroup (Engel group) is a group in which every element is an Engel
element. -/
def IsEngelGroup (G : Type*) [Group G] : Prop :=
  ∀ y : G, IsEngelElement y

/--
Is a group a nilgroup if it is the product of two normal nilsubgroups?

Since $H$ and $K$ are normal, the product $HK$ coincides with the join
$H \sqcup K$, so "$G$ is the product of $H$ and $K$" is stated as
$H \sqcup K = G$.
-/
@[category research open, AMS 20]
theorem kourovka.«1.40» : answer(sorry) ↔
    ∀ (G : Type) [Group G] (H K : Subgroup G),
      H.Normal → K.Normal → IsEngelGroup H → IsEngelGroup K → H ⊔ K = ⊤ →
      IsEngelGroup G := by
  sorry

end Kourovka.«1.40»
