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
# Erdős Problem 539

In this problem, a function $h : \mathbb{N} \to\mathbb{N}$ is defined maximally by a specified
counting property.

The problem asks to estimate $h(n)$. This has been interpreted here as asking for $\Theta(h(n))$.
The principal version includes `answer(sorry)` for an unknown function. On the other hand, the best
known upper bound is $n^{2/3}$ and the best known lower bound is $\sqrt{n}$ so we
also provide these candidates as variants. Moreover, it suffices to show $O(h(n))$ and
$O(\sqrt{n})$ respectively for each, so further variants are provided for those.

In the source paper [Er73], Erdős also remarks that it should not be too difficult
to determine $\lim_{n\to\infty}\log(h(n))/\log(n)$. This does not appear on the website, and
it is not clear whether this remains open, but we include it here either way.

*References:*
- [erdosproblems.com/539](https://www.erdosproblems.com/539)
- [GR99] Granville, A., & Roesler, F. (1999). _The Set of Differences of a Given Set_. The American Mathematical Monthly, 106(4), 338–344.
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.
-/

open Filter

open scoped Asymptotics Finset

namespace Erdos539

/-- We say that $m$ is a cofactor lower bound for a given $n$ if, for every set $A$ of $n$
non-negative integers, there are at least $m$ cofactors $a / (a, b)$, where $a, b\in A$.-/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

/-- The cofactor threshold $h(n)$, for every positive $n$, is the largest cofactor lower bound
for $n$. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

/-- Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the
set\[\left\{ \frac{a}{(a,b)}: a,b\in A\right\}\]has size at least $h(n)$. Estimate $h(n)$. -/
@[category research open, AMS 5 11]
theorem erdos_539 :
    (fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the
set\[\left\{ \frac{a}{(a,b)}: a,b\in A\right\}\]has size at least $h(n)$.
Is $h(n) = \Theta(\sqrt{n})$? -/
@[category research open, AMS 5 11]
theorem erdos_539.variants.sq :
    (fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] fun n ↦ √n := by
  sorry

/-- Erdős and Szemerédi proved that\[n^{1/2} \ll h(n)\]. -/
@[category research solved, AMS 5 11]
theorem erdos_539.variants.sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := by
  sorry

/-- To prove `erdos_539.variants.sq` it suffices to show \[ h(n)\ll n^{1/2}\]. -/
@[category research open, AMS 5 11]
theorem erdos_539.variants.isBigO_sq :
    (fun n ↦ (cofactorThreshold n : ℝ)) =O[atTop] fun n ↦ √n := by
  sorry

/-- Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the
set\[\left\{ \frac{a}{(a,b)}: a,b\in A\right\}\]has size at least $h(n)$.
Is $h(n) = \Theta(n^{2/3})$? -/
@[category research open, AMS 5 11]
theorem erdos_539.variants.sq_cube_root :
    (fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] fun n ↦ (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

/-- Granville and Roesler [GR99] showed that \[h(n)\ll n^{2/3}\].-/
@[category research solved, AMS 5 11]
theorem erdos_539.variants.isBigO_sq_cube_root :
    (fun n ↦ (cofactorThreshold n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

/-- To prove `erdos_539.variants.sq_cube_root` it suffices to show \[n^{2/3}\ll h(n)\]. -/
@[category research open, AMS 5 11]
theorem erdos_539.variants.sq_cube_root_isBigO :
    (fun n : ℕ ↦ (n : ℝ) ^ ((2 : ℝ) / 3)) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := by
  sorry

/-- From [Er73]: The determination of
$$
  \lim_{n\to\infty}\frac{\log(h(n))}{\log(n)}
$$
will perhaps be not too difficult.
-/
-- Formalisation note: it is not clear if this problem has since been solved
@[category research open, AMS 5 11]
theorem erdos_539.variants.limit :
    atTop.Tendsto (fun n ↦ Real.log (cofactorThreshold n) / Real.log n) answer(sorry) := by
  sorry

end Erdos539
