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
# Erdős Problem 789

In this problem, a function $h : \mathbb{N} \to\mathbb{N}$ is defined maximally by
some counting property.

The problem asks to estimate $h(n)$. This has been interpreted here as asking for $\Theta(h(n))$.
The principal version includes `answer(sorry)` for an unknown function. On the other hand, the best
known upper bound is $\sqrt{n}$ and the best known lower bound is $(n\log(n))^{1/3}$ so we
also provide these candidates as variants. Moreover, it suffices to show $O(h(n))$ and
$O((n\log(n))^{1/3})$ respectively for each, so further variants are provided for those.

*References:*
- [erdosproblems.com/789](https://www.erdosproblems.com/789)
- [Str66] Straus, E. G., _On a problem in combinatorial number theory_. J. Math. Sci. (1966), 77--80.
- [Er62c] Erdős, Pál, _Some remarks on number theory_. {III}. Mat. Lapok (1962), 28--38.
- [Ch74b] Choi, S. L. G., _On an extremal problem in number theory_. J. Number Theory (1974), 105--111.
-/

open Filter

open scoped Asymptotics Finset

namespace Erdos789

/-- Given a non-negative integer $n$, we say $m$ is a separating cardinality of
subset sums if, for any set $A$ of $n$ integers, there is some $B\subseteq A$ of
size $\geq m$ such that subset sums of $B$ can only ever coincide when the
subsets have the same cardinality. -/
def IsSubsetSumSeparatingCard (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, #A = n → ∃ B : Finset ℤ, B ⊆ A ∧ m ≤ #B ∧
    (∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S)

/-- The subset sum threshold $h(n)$, for each positive $n$, is the maximal separating
cardinality of subset sums for $n$. -/
noncomputable def subsetSumThreshold (n : ℕ): ℕ :=
  sSup { m | IsSubsetSumSeparatingCard n m }

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Estimate $h(n)$.
-/
@[category research open, AMS 5]
theorem erdos_789 :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Is $h(n) = \Theta(\sqrt{n})$?
-/
@[category research open, AMS 5]
theorem erdos_789.variants.sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] fun n ↦ √n := by
  sorry

/-- Straus [Str66] proved that $h(n) \ll \sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.isBigO_sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop] fun n ↦ √n := by
  sorry

/-- By the solved variant `erdos_789.variants.isBigO_sq`, in order to prove
`erdos_789.variants.sq` it suffices to show $\sqrt{n}=O(h(n))$. -/
@[category research open, AMS 5]
theorem erdos_789.variants.sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (subsetSumThreshold n : ℝ) := by
  sorry

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Is $h(n) = \Theta((n\log(n)))^{1/3})$?
-/
@[category research open, AMS 5]
theorem erdos_789.variants.cube_root_linearithmic :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop]
      fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3) := by
  sorry

/-- Erdős [Er62c] and Choi [Ch74b] proved that $(n\log(n))^{1/3}\ll h(n)$. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.cube_root_linearithmic_isBigO :
    (fun n : ℕ ↦ (n * Real.log n) ^ ((1 : ℝ) / 3)) =O[atTop]
      fun n ↦ (subsetSumThreshold n : ℝ) := by
  sorry

/-- By the solved variant `erdos_789.variants.cube_root_linearithmic_isBigO`, in order to prove
`erdos_789.variants.cube_root_linarithmic` it suffices to show $h(n) = O((n\log(n))^{1/3})$. -/
@[category research open, AMS 5]
theorem erdos_789.variants.isBigO_cube_root_linearithmic :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop]
      fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3) := by
  sorry

end Erdos789
