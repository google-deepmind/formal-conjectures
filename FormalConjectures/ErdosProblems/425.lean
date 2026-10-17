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

*Reference:* [Erdős Problem 425](https://www.erdosproblems.com/425)
-/

@[expose] public section

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

/-- Products of two distinct elements are distinct exactly when pairwise products are. -/
@[category test, AMS 5 11]
theorem rProductsDistinct_two : RProductsDistinct 2 = PairProductDistinct := by
  funext A
  apply propext
  have sorted_pair (S : Finset ℕ) (hS : S.card = 2) :
      ∃ a b, a < b ∧ S = {a, b} := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    rcases lt_or_gt_of_ne hab with hab | hab
    · exact ⟨a, b, hab, rfl⟩
    · exact ⟨b, a, hab, Finset.pair_comm a b⟩
  constructor
  · intro h a b c d ha hb hc hd hab hcd hp
    have heq : ({a, b} : Finset ℕ) = {c, d} :=
      h (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
          And.intro ha hb)
        (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
          And.intro hc hd)
        (Finset.card_pair hab.ne) (Finset.card_pair hcd.ne)
        (by simpa [Finset.prod_pair hab.ne, Finset.prod_pair hcd.ne] using hp)
    have ha' : a ∈ ({c, d} : Finset ℕ) := heq ▸ (by simp)
    have hb' : b ∈ ({c, d} : Finset ℕ) := heq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
    omega
  · intro h S T hSA hTA hS hT hp
    obtain ⟨a, b, hab, rfl⟩ := sorted_pair S hS
    obtain ⟨c, d, hcd, rfl⟩ := sorted_pair T hT
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hSA hTA
    obtain ⟨rfl, rfl⟩ := h hSA.1 hSA.2 hTA.1 hTA.2 hab hcd
      (by simpa [Finset.prod_pair hab.ne, Finset.prod_pair hcd.ne] using hp)
    rfl

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
