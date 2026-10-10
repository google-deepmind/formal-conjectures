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
# Erdős Problem 425

*Reference:* [Erdős Problem 425](https://www.erdosproblems.com/425)
-/

namespace Erdos425

open Filter
open scoped Topology

/-- A finite set has distinct pairwise products if $ab = cd$, for elements satisfying
$a < b$ and $c < d$, implies $(a,b) = (c,d)$. -/
def PairProductDistinct (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a < b → c < d →
      a * b = c * d → a = c ∧ b = d

/-- The maximum cardinality $F(n)$ of a subset of $\{1,\ldots,n\}$ with distinct
pairwise products. -/
noncomputable def pairProductExtremal (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun m => ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ PairProductDistinct A ∧ A.card = m) n

/--
For `r`, all products over `r` distinct elements of `A` are distinct.  We use
finite subsets of `A` of cardinality exactly `r`.
-/
def RProductsDistinct (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ ⦃S T : Finset ℕ⦄,
    S ⊆ A → T ⊆ A → S.card = r → T.card = r → S.prod id = T.prod id → S = T

/-- Let $F(n)$ be the maximum size of a subset of $\{1,\ldots,n\}$ with distinct
pairwise products. Is there a constant $c > 0$ such that
$$F(n) = \pi(n) + (c + o(1)) n^{3/4}(\log n)^{-3/2}?$$ -/
@[category research open, AMS 5 11]
theorem erdos_425.parts.i : answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧
    Tendsto
      (fun n : ℕ =>
        ((pairProductExtremal n : ℝ) - (Nat.primeCounting n : ℝ)) /
          ((n : ℝ) ^ ((3 : ℝ) / 4) * (Real.log n) ^ (-(3 : ℝ) / 2)))
      atTop (𝓝 c) := by
  sorry

/-- If all products of $r$ distinct elements of $A \subseteq \{1,\ldots,n\}$ are
distinct, must
$$|A| \leq \pi(n) + O\bigl(n^{(r+1)/(2r)}\bigr)?$$ -/
@[category research open, AMS 5 11]
theorem erdos_425.parts.ii : answer(sorry) ↔ ∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → RProductsDistinct r A →
      (A.card : ℝ) ≤ (Nat.primeCounting n : ℝ) +
        C * (n : ℝ) ^ (((r : ℝ) + 1) / (2 * r)) := by
  sorry

end Erdos425
