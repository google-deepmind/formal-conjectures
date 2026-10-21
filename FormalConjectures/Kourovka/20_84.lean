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

public import FormalConjecturesUtil

/-!
# Problem 20.84

by E. Rips

*References:*
* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v49), Problem 20.84.
* [Pa68] I. B. S. Passi, *Dimension subgroups*, J. Algebra 9 (1968), 152–182.
* [Ri72] E. Rips, *On the fourth integer dimension subgroup*, Israel J. Math. 12 (1972),
  342–346.
* [Mi21] R. Mikhailov, *Homotopy patterns in group theory*, Proc. ICM 2022,
  [arXiv:2111.00737](https://arxiv.org/abs/2111.00737).
* [Pa79] I. B. S. Passi, *Group rings and their augmentation ideals*, Lecture Notes in Math. 715,
  Springer, 1979.
* [Ta81] K.-I. Tahara, *The augmentation quotients of group rings and the fifth dimension
  subgroups*, J. Algebra 71 (1981), 141–173.
* [MP09] R. Mikhailov, I. B. S. Passi, *Lower central and dimension series of groups*,
  Lecture Notes in Math. 1952, Springer, 2009.
* [IMP26] V. Ionin, R. Mikhailov, T. Petrov, *Dimension subrings of Lie rings*,
  [arXiv:2610.02042](https://arxiv.org/abs/2610.02042) (2026).

`Group.dimensionSubgroup n G` is the integral dimension subgroup
$D_n(G) = \{g \in G \mid g - 1 \in \Delta^n\}$, where $\Delta$ is the augmentation ideal of
$\mathbb{Z}[G]$. Mathlib's lower central series is indexed from `0`:
`(⊤ : Subgroup G).lowerCentralSeries k` is $\gamma_{k+1}(G)$. For example,
$\gamma_4(G)$ is `(⊤ : Subgroup G).lowerCentralSeries 3`.

One always has $\gamma_n(G) \subseteq D_n(G)$, with equality for $n \le 3$ but not for $n = 4$.
-/

@[expose] public section

open Group

namespace Kourovka.«20.84»

/--
Does there exist a nilpotent group of class $3$ with a non-trivial $5$-th dimension subgroup?
-/
@[category research open, question, AMS 16 20]
theorem kourovka_20_84 :
    ∃ (G : Type) (_ : Group G), Group.IsNilpotent G ∧ Group.nilpotencyClass G = 3 ∧
      dimensionSubgroup 5 G ≠ ⊥ := by
  sorry

/--
Is $D_5(G) \subseteq \gamma_4(G)$ for every group $G$?

This is the form in which Problem 20.84 is quoted in [IMP26, §1.3]. A negative answer to it
is equivalent to a positive answer to `kourovka_20_84`: if $g \in D_5(G) \setminus \gamma_4(G)$,
then the image of $g$ in $G / \gamma_4(G)$ is a non-trivial element of $D_5$ of a group of
class at most $3$, and groups of class at most $2$ have
$D_5 \subseteq D_3 = \gamma_3 = 1$ (`kourovka_20_84.variants.d_three`).
-/
@[category research open, question, AMS 16 20]
theorem kourovka_20_84.variants.d_five_le_gamma_four :
    ∀ (G : Type) [Group G], dimensionSubgroup 5 G ≤ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  sorry

/--
$D_2(G) = \gamma_2(G) = [G, G]$ for every group $G$ (classical; see [Pa79], [MP09]).
-/
@[category research solved, AMS 16 20, formal_proof using lean4 at
  "https://github.com/ispacex/dimension-subrings/blob/9b7df29337dd27bcee8ea20710fc9434492a89ce/groups/GroupDimension/DTwo.lean#L97"]
theorem kourovka_20_84.variants.d_two (G : Type) [Group G] :
    dimensionSubgroup 2 G = commutator G := by
  sorry

/--
$D_3(G) = \gamma_3(G)$ for every group $G$ (G. Higman, R. Rees; Passi [Pa68]; see [Pa79],
[MP09]).
-/
@[category research solved, AMS 16 20]
theorem kourovka_20_84.variants.d_three (G : Type) [Group G] :
    dimensionSubgroup 3 G = (⊤ : Subgroup G).lowerCentralSeries 2 := by
  sorry

/--
Rips [Ri72] constructed a finite $2$-group $G$ with $D_4(G) \ne \gamma_4(G)$; its order is
$2^{38}$ according to [Mi21, §5]. So the equality $D_n = \gamma_n$ fails for $n = 4$.
-/
@[category research solved, AMS 16 20]
theorem kourovka_20_84.variants.rips :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPGroup 2 G ∧
      dimensionSubgroup 4 G ≠ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  sorry

/--
For every group $G$ the quotient $D_4(G) / \gamma_4(G)$ has exponent dividing $2$, that is,
$g^2 \in \gamma_4(G)$ for all $g \in D_4(G)$ (Passi [Pa68]; see [MP09]).
-/
@[category research solved, AMS 16 20]
theorem kourovka_20_84.variants.d_four_sq (G : Type) [Group G] :
    ∀ g ∈ dimensionSubgroup 4 G, g ^ 2 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  sorry

/--
For every finite group $G$ the quotient $D_5(G) / \gamma_5(G)$ has exponent dividing $6$, that
is, $g^6 \in \gamma_5(G)$ for all $g \in D_5(G)$ (Tahara [Ta81, Cor. 6.11]).
-/
@[category research solved, AMS 16 20]
theorem kourovka_20_84.variants.tahara (G : Type) [Group G] [Finite G] :
    ∀ g ∈ dimensionSubgroup 5 G, g ^ 6 ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := by
  sorry

/-- $D_1(G) = G$. -/
@[category test, AMS 16 20]
theorem dimensionSubgroup_one_test (G : Type) [Group G] : dimensionSubgroup 1 G = ⊤ :=
  dimensionSubgroup_one

/-- The dimension series is decreasing: $D_5(G) \subseteq D_4(G)$. -/
@[category test, AMS 16 20]
theorem dimensionSubgroup_five_le_four (G : Type) [Group G] :
    dimensionSubgroup 5 G ≤ dimensionSubgroup 4 G :=
  dimensionSubgroup_antitone (by norm_num)

end Kourovka.«20.84»
