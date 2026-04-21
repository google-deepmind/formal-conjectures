/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 170

*Reference:* [erdosproblems.com/170](https://www.erdosproblems.com/170)
-/

open scoped Topology

namespace Erdos170

/-- An $N$-perfect ruler is a finite subset $A \subseteq \mathbb{N}$ (the marks), such that each
positive integer $k \leq N$ can be measured, that is, expressed as a difference $k = a_1 - a_0$
with $a_0, a_1 \in A$. The set $A$ is then also called a difference basis w.r.t. $N$. -/
@[reducible]
def PerfectRuler (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ k ∈ Finset.range (N + 1), ∃ᵉ (a₀ ∈ A) (a₁ ∈ A), k = a₁ - a₀

/-- We define the set of all $N$-perfect rulers $A$ of length $N$, i.e.
subsets $A \subseteq \{0, \dots, N\}$, s.t. $A$ is $N$-perfect.
This is also called a restricted difference basis w.r.t. $N$. -/
def PerfectRulersLengthN (N : ℕ) :
    Finset (Finset ℕ) := (Finset.range (N + 1)).powerset.filter (PerfectRuler N)

/-- The trivial ruler with all marks $\{0, \dots, N\}$. -/
abbrev TrivialRuler (N : ℕ) : Finset ℕ := Finset.range (N+1)

/-- Sanity Check: the trivial ruler is actually a perfect ruler if $K \geq N$ -/
@[category API, AMS 05]
lemma trivial_ruler_is_perfect (N : ℕ) : TrivialRuler N ∈ PerfectRulersLengthN N := by
    simp only [PerfectRulersLengthN, Finset.mem_filter, Finset.mem_powerset, Finset.range_subset]
    exact ⟨by simp, fun k hk => ⟨0, by simp, k, hk, rfl⟩⟩

/-- We define a function `F N` as the minimum cardinality of an `N`-perfect ruler of length `N`. -/
def F (N : ℕ) : ℕ :=
    Finset.min' (Finset.image Finset.card (PerfectRulersLengthN N))
                (Finset.image_nonempty.mpr ⟨TrivialRuler N, trivial_ruler_is_perfect N⟩)

/-- The problem is to determine the limit of the sequence $\frac{F(N)}{\sqrt{N}}$ as $N \to \infty$. -/
@[category research open, AMS 05]
lemma erdos170 : Filter.Tendsto (fun N => F N / √N) Filter.atTop (𝓝 answer(sorry)) := by sorry

/-- A known lower bound to the limit by Leech [Le56], which is $1.56\dots$. -/
noncomputable abbrev lower_bound := √(sSup {2 * (1 - Real.sin θ / θ) | θ ≠ 0})
/-- A known upper bound obtained by constructing Wichmann's Rulers [Wi63]. -/
noncomputable abbrev upper_bound := √3

/-- The existence of the limit has been proved by Erdős and Gál [ErGa48].
The lower bound has been proven by Leech [Le56], who refined an argument of Rédei and Rényi.
The upper bound is due to Wichmann [Wi63]. -/
@[category research solved, AMS 05]
lemma erdos170.existing_bounds :
  ∃ x ∈ Set.Icc lower_bound upper_bound,
    Filter.Tendsto (fun N => F N / √N) Filter.atTop (𝓝 x) := by sorry

end Erdos170
