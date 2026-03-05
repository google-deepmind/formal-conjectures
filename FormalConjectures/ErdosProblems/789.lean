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

*Reference:* [erdosproblems.com/789](https://www.erdosproblems.com/789)

Let $h(n)$ be maximal such that if $A \subseteq \mathbb{Z}$ with $|A| = n$ then there is
$B \subseteq A$ with $|B| \geq h(n)$ such that if $a_1 + \cdots + a_r = b_1 + \cdots + b_s$
with $a_i, b_i \in B$ then $r = s$.

Estimate $h(n)$.

Erdős [Er62c] proved $h(n) \ll n^{5/6}$. Straus [St66] proved $h(n) \ll n^{1/2}$.
Erdős noted $h(n) \gg n^{1/3}$. Erdős [Er62c] and Choi [Ch74b] improved the
lower bound to $h(n) \gg (n \log n)^{1/3}$.
-/

namespace Erdos789

/-- A subset $B$ of $\mathbb{Z}$ has the "sum-length property" if whenever
$a_1 + \cdots + a_r = b_1 + \cdots + b_s$ with all $a_i, b_j \in B$, then $r = s$. -/
def SumLengthProperty (B : Finset ℤ) : Prop :=
  ∀ (as bs : List ℤ), (∀ a ∈ as, a ∈ B) → (∀ b ∈ bs, b ∈ B) →
    as.sum = bs.sum → as.length = bs.length

/-- $h(n)$ is the maximal $h$ such that every $n$-element subset $A$ of $\mathbb{Z}$ contains a
subset $B$ of size $\geq h$ with the sum-length property. -/
noncomputable def erdos789_h (n : ℕ) : ℕ :=
  sSup { h : ℕ | ∀ (A : Finset ℤ), A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ h ≤ B.card ∧ SumLengthProperty B }

/--
Erdős Problem 789, upper bound (Straus [St66]):
$h(n) \ll n^{1/2}$, i.e., there exists $C > 0$ such that $h(n) \leq C \cdot n^{1/2}$
for all $n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_789 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ,
      (erdos789_h n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Erdős Problem 789, lower bound (Erdős [Er62c] and Choi [Ch74b]):
$h(n) \gg (n \log n)^{1/3}$, i.e., there exist $C > 0$ and $N_0$ such that for all
$n \geq N_0$, $h(n) \geq C \cdot (n \cdot \log n)^{1/3}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_789.variants.lower_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos789_h n : ℝ) ≥ C * ((n : ℝ) * Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) := by
  sorry

end Erdos789
