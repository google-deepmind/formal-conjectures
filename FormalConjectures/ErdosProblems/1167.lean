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
# Erdős Problem 1167

*Reference:* [erdosproblems.com/1167](https://www.erdosproblems.com/1167)
-/

open Cardinal Ordinal Combinatorics

namespace Erdos1167

universe u

/--
**Erdős Problem 1167.** Let $r \geq 2$ be finite and $\lambda$ be an infinite
cardinal. Let $\kappa_\alpha$ be cardinals for all $\alpha < \gamma$. Is it true
that
$$2^\lambda \to (\kappa_\alpha + 1)_{\alpha < \gamma}^{r+1}$$
implies
$$\lambda \to (\kappa_\alpha)_{\alpha < \gamma}^r?$$
Here $+$ means cardinal addition, so that $\kappa_\alpha + 1 = \kappa_\alpha$
if $\kappa_\alpha$ is infinite.

A problem of Erdős, Hajnal, and Rado.
-/
@[category research open, AMS 5]
theorem erdos_1167 : answer(sorry) ↔
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (lam : Cardinal.{u}), ℵ₀ ≤ lam →
    ∀ (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}),
      cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ (fun α => κ α + 1) →
      cardinalPartitionRel lam r γ κ := by
  sorry

namespace erdos_1167.variants

/--
**Finite-target case.** When all $\kappa_\alpha$ are finite, $\kappa_\alpha + 1$
is the ordinary natural-number successor. Special case of `erdos_1167`.
-/
@[category research open, AMS 5]
theorem finite_targets (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u})) := by
  sorry

/--
**Binary-color case.** The $\gamma = 2$ specialization (two color classes).
-/
@[category research open, AMS 5]
theorem binary_colors (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (κ : (2 : Ordinal.{u}).ToType → Cardinal.{u}) :
    cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) 2 (fun α => κ α + 1) →
    cardinalPartitionRel lam r 2 κ := by
  sorry

/--
**Infinite-target case.** When all $\kappa_\alpha \geq \aleph_0$ are infinite,
$\kappa_\alpha + 1 = \kappa_\alpha$, so the hypothesis simplifies to a "pure"
stepping-down lemma:
$$2^\lambda \to (\kappa_\alpha)_{\alpha<\gamma}^{r+1} \implies
   \lambda \to (\kappa_\alpha)_{\alpha<\gamma}^r.$$
-/
@[category research open, AMS 5]
theorem infinite_targets (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}) (hκ : ∀ i, ℵ₀ ≤ κ i) :
    cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ κ →
    cardinalPartitionRel lam r γ κ := by
  sorry

/--
**$r = 2$ case.** The stepping-down from 3-uniform to 2-uniform partition
relations: $2^\lambda \to (\kappa_\alpha + 1)_{\alpha<\gamma}^3$ implies
$\lambda \to (\kappa_\alpha)_{\alpha<\gamma}^2$. Generalises the classical
Erdős–Rado stepping-up/down theorem for pairs.
-/
@[category research open, AMS 5]
theorem r_eq_two (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}) :
    cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) 3 γ (fun α => κ α + 1) →
    cardinalPartitionRel lam 2 γ κ := by
  sorry

end erdos_1167.variants

end Erdos1167
