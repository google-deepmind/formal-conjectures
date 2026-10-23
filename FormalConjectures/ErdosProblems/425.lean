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
# Erdős Problem 425

*References:*
- [erdosproblems.com/425](https://www.erdosproblems.com/425)
- [Er69] Erdős, P., *Some applications of graph theory to number theory*.
  The Many Facets of Graph Theory (1969), 77-82.
- [Er70b] Erdős, P., *Some applications of graph theory to number theory*.
  Proc. Second Chapel Hill Conf. on Combinatorial Mathematics and its Applications
  (1970), 136-145.
-/

@[expose] public section

namespace Erdos425

open Filter
open scoped Topology

/-- All products of $r$ distinct elements of $A$ are distinct. Each increasing tuple is
represented by its underlying $r$-element subset. -/
def HasDistinctProducts (r : ℕ) (A : Finset ℕ) : Prop :=
  Set.InjOn (fun B : Finset ℕ ↦ ∏ b ∈ B, b) {B | B ⊆ A ∧ B.card = r}

/-- The maximum size of a subset of $\{1,\ldots,n\}$ with distinct products of two
distinct elements. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter (HasDistinctProducts 2)).sup Finset.card

/-- The empty set has distinct products for every product length. -/
@[category test, AMS 5 11]
theorem hasDistinctProducts_empty (r : ℕ) : HasDistinctProducts r ∅ := by
  intro B hB C hC _
  have hB0 := Finset.subset_empty.mp hB.1
  have hC0 := Finset.subset_empty.mp hC.1
  exact hB0.trans hC0.symm

/-- The empty interval has maximum cardinality zero. -/
@[category test, AMS 5 11]
theorem F_zero : F 0 = 0 := by
  simp [F]

/--
Let $F(n)$ be the maximum possible size of a subset $A\subseteq\{1,\ldots,n\}$ such that
the products $ab$ are distinct for all $a<b$. Is there a constant $c$ such that
$$F(n)=\pi(n)+(c+o(1))n^{3/4}(\log n)^{-3/2}?$$
-/
@[category research open, AMS 5 11]
theorem erdos_425.parts.i : answer(sorry) ↔
    ∃ c : ℝ, Tendsto (fun n : ℕ ↦ ((F n : ℝ) - Nat.primeCounting n) /
      ((n : ℝ) ^ ((3 : ℝ) / 4) * (Real.log n) ^ (-(3 : ℝ) / 2))) atTop (𝓝 c) := by
  sorry

/--
If $A\subseteq \{1,\ldots,n\}$ is such that all products $a_1\cdots a_r$ are distinct
for $a_1<\cdots<a_r$ then is it true that
$$\lvert A\rvert \leq \pi(n)+O(n^{\frac{r+1}{2r}})?$$

Here $r\geq 1$, and the implied constant may depend on $r$.
-/
@[category research open, AMS 5 11]
theorem erdos_425.parts.ii : answer(sorry) ↔
    ∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        HasDistinctProducts r A → (A.card : ℝ) ≤ Nat.primeCounting n +
          C * (n : ℝ) ^ (((r : ℝ) + 1) / (2 * r)) := by
  sorry

end Erdos425
