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
# Erdős Problem 1022

*References:*
- [erdosproblems.com/1022](https://www.erdosproblems.com/1022)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Lo68] Lovász, L., *On covering of graphs*. Theory of Graphs (Proc. Colloq., Tihany, 1966)
  (1968), 231-236.
- [Wo13b] Wood, D. R., *Hypergraph colouring and degeneracy*. arXiv:1310.2972 (2013).
-/

namespace Erdos1022

/-- A family `F` of finite sets has **property B** (equivalently, chromatic number `2`) if
there is a `2`-colouring of the ground set under which no member of `F` is monochromatic. -/
def HasPropertyB (F : Finset (Finset ℕ)) : Prop :=
  ∃ f : ℕ → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

/-- `SparseImpliesPropertyB t c` asserts that every finite family `F` of finite sets, all of
size at least `t`, such that for every nonempty finite set `X` there are `< c * |X|` many
`A ∈ F` with `A ⊆ X`, has property B. -/
def SparseImpliesPropertyB (t : ℕ) (c : ℝ) : Prop :=
  ∀ F : Finset (Finset ℕ), (∀ A ∈ F, t ≤ A.card) →
    (∀ X : Finset ℕ, X.Nonempty → ((F.filter (· ⊆ X)).card : ℝ) < c * (X.card : ℝ)) →
    HasPropertyB F

/--
Is there a constant $c_t$, where $c_t\to \infty$ as $t\to \infty$, such that if $\mathcal{F}$
is a finite family of finite sets, all of size at least $t$, and for every set $X$ there are
$<c_t\lvert X\rvert$ many $A\in \mathcal{F}$ with $A\subseteq X$, then $\mathcal{F}$ has
chromatic number $2$ (in other words, has property B)?

This is false, and $c_t<2$ for all $t$: a counterexample is provided by Wood [Wo13b], who
constructs, for any $r\geq 2$, a triangle-free $2$-degenerate $r$-uniform hypergraph with
chromatic number $3$. A similar counterexample was found independently by KoishiChan in the
comments.
-/
@[category research solved, AMS 5]
theorem erdos_1022 : answer(False) ↔
    ∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
      ∀ t : ℕ, SparseImpliesPropertyB t (c t) := by
  sorry

/--
This is false, and $c_t<2$ for all $t$: a counterexample is provided by Wood [Wo13b], who
constructs, for any $r\geq 2$, a triangle-free $2$-degenerate $r$-uniform hypergraph with
chromatic number $3$. A similar counterexample was found independently by KoishiChan in the
comments.
-/
@[category research solved, AMS 5]
theorem erdos_1022.variants.lt_two : answer(True) ↔
    ∀ (t : ℕ) (c : ℝ), SparseImpliesPropertyB t c → c < 2 := by
  sorry

/--
Erdős originally conjectured, in this language, that $c_2=1$, which he reports in [Er71] was
proved by Lovász.
-/
@[category research solved, AMS 5]
theorem erdos_1022.variants.lovasz :
    IsGreatest {c : ℝ | SparseImpliesPropertyB 2 c} 1 := by
  sorry

end Erdos1022
