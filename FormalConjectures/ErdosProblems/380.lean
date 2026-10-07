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
# Erdős Problem 380

*References:*
- [erdosproblems.com/380](https://www.erdosproblems.com/380)
- [Ta26c] Tao, T., arXiv:2603.27990 (2026).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos380

/-- An integer $n > 1$ is *bad* if its greatest prime factor $P(n)$ satisfies $P(n)^2 \mid n$.
Note that $1$ is not bad. -/
def IsBad (n : ℕ) : Prop := 1 < n ∧ n.maxPrimeFac ^ 2 ∣ n

/-- An interval $[u, v]$ of positive integers is *bad* if the greatest prime factor of
$\prod_{u \leq m \leq v} m$ occurs with exponent greater than $1$. -/
def IsBadInterval (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ IsBad (∏ m ∈ Finset.Icc u v, m)

/-- $B(x)$ counts the integers $n \leq x$ which are contained in at least one bad interval.
The bad interval itself is not required to be contained in $[1, x]$. -/
noncomputable def B (x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ u v, IsBadInterval u v ∧ u ≤ n ∧ n ≤ v}.ncard

/-- $S(x)$ counts the integers $n \leq x$ such that $P(n)^2 \mid n$, where $P(n)$ is the largest
prime factor of $n$. -/
noncomputable def S (x : ℕ) : ℕ := {n : ℕ | n ≤ x ∧ IsBad n}.ncard

/--
We call an interval $[u,v]$ 'bad' if the greatest prime factor of $\prod_{u\leq m\leq v}m$ occurs
with an exponent greater than $1$. Let $B(x)$ count the number of $n\leq x$ which are contained in
at least one bad interval. Is it true that
$$B(x)\sim \#\{ n\leq x: P(n)^2\mid n\},$$
where $P(n)$ is the largest prime factor of $n$?

This was proved by Tao [Ta26c], in the stronger form
$$B(x) = \left(1+O((\log x)^{-1+o(1)})\right) \#\{ n\leq x: P(n)^2\mid n\}.$$
-/
@[category research solved, AMS 11]
theorem erdos_380 : answer(True) ↔
    (fun x : ℕ ↦ (B x : ℝ)) ~[atTop] (fun x : ℕ ↦ (S x : ℝ)) := by
  sorry

/-- An interval $[u, v]$ of positive integers is *very bad* if $\prod_{u \leq m \leq v} m$ is
powerful. -/
def IsVeryBadInterval (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ (∏ m ∈ Finset.Icc u v, m).Powerful

/-- The number of integers $1 \leq n \leq x$ which are contained in at least one very bad
interval. -/
noncomputable def veryBadCount (x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ u v, IsVeryBadInterval u v ∧ u ≤ n ∧ n ≤ v}.ncard

/-- The number of powerful numbers $1 \leq n \leq x$. -/
noncomputable def powerfulCount (x : ℕ) : ℕ := {n : ℕ | 1 ≤ n ∧ n ≤ x ∧ n.Powerful}.ncard

/--
Erdős and Graham also asked about 'very bad' intervals $[u,v]$, those for which
$\prod_{u\leq m\leq v}m$ is powerful: the number of $n\leq x$ contained in at least one very bad
interval should be asymptotic to the number of powerful numbers $\leq x$.

Tao [Ta26c] proved that the number of $n\leq x$ which are contained in a very bad interval but are
not themselves powerful is $O(x^{2/5+o(1)})$, which implies this.
-/
@[category research solved, AMS 11]
theorem erdos_380.variants.very_bad :
    (fun x : ℕ ↦ (veryBadCount x : ℝ)) ~[atTop] (fun x : ℕ ↦ (powerfulCount x : ℝ)) := by
  sorry

end Erdos380
