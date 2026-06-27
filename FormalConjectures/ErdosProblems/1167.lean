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

The original Erdős–Hajnal problem list gives the additional conditions $\gamma \geq 2$, $r < \omega$,
and $\kappa_\alpha > r$. Without $\gamma \geq 2$, the statement is false: taking $\gamma = 1$ and
$\kappa_0 = \aleph_1$ with $\lambda = \aleph_0$ gives a counterexample, since the partition relation
with one color degenerates to a cardinality comparison (see `erdos_1167.unrestricted_is_false`).
-/

open Cardinal Ordinal Combinatorics

namespace Erdos1167

universe u

/--
**Erdős Problem 1167.** Let $r \geq 2$ be finite, $\gamma \geq 2$, and $\lambda$ be an infinite
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
    ∀ (γ : Ordinal.{u}), 2 ≤ γ →
    ∀ (κ : γ.ToType → Cardinal.{u}),
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
    (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ) :
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
**Infinite-target case.** When all $\kappa_\alpha \geq \aleph_0$ are infinite and bounded by
$\lambda$, $\kappa_\alpha + 1 = \kappa_\alpha$, so the hypothesis simplifies to a "pure"
stepping-down lemma:
$$2^\lambda \to (\kappa_\alpha)_{\alpha<\gamma}^{r+1} \implies
   \lambda \to (\kappa_\alpha)_{\alpha<\gamma}^r.$$
The condition $\kappa_\alpha \leq \lambda$ is needed to avoid a size obstruction: without it, the
conclusion would require a subset of $\lambda$ of size $\kappa_\alpha > \lambda$, which is impossible
(see `infinite_targets_needs_bound`).
-/
@[category research open, AMS 5]
theorem infinite_targets (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (κ : γ.ToType → Cardinal.{u}) (hκ : ∀ i, ℵ₀ ≤ κ i)
    (hκ_le : ∀ i, κ i ≤ lam) :
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
    (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (κ : γ.ToType → Cardinal.{u}) :
    cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) 3 γ (fun α => κ α + 1) →
    cardinalPartitionRel lam 2 γ κ := by
  sorry

end erdos_1167.variants

/- ## Counterexample for the unrestricted statement

The partition relation $\mu \to (\nu)^r_1$ with a single color ($\gamma = 1$) degenerates to the
cardinality comparison $\nu \leq \mu$. Using this, we show the unrestricted version of Erdős
Problem 1167 (without $\gamma \geq 2$) is false.
-/

/-- A canonical element of the type `(1 : Ordinal).ToType`. -/
noncomputable def i0 : (1 : Ordinal.{u}).ToType := default

/--
The partition relation $\mu \to (\nu)^r_1$ with a single color is equivalent to $\nu \le \mu$.
-/
@[category API, AMS 5]
lemma cardinalPartitionRel_one (μ : Cardinal.{u}) (r : ℕ)
    (ν : (1 : Ordinal.{u}).ToType → Cardinal.{u}) :
    cardinalPartitionRel μ r 1 ν ↔ μ ≥ ν i0 := by
  dsimp [cardinalPartitionRel]
  constructor
  · intro h
    have hA : #(μ.out) = μ := Cardinal.mk_out μ
    rcases h μ.out hA (fun _ => i0) with ⟨i, H, hH, _⟩
    have hi : i = i0 := Subsingleton.elim i i0
    subst hi
    have hle : #H ≤ #(μ.out) := Cardinal.mk_set_le H
    rw [hH, hA] at hle
    exact hle
  · intro h A hA col
    have hle : ν i0 ≤ #A := by rwa [hA]
    rcases Cardinal.le_mk_iff_exists_set.mp hle with ⟨H, hH⟩
    use i0, H, hH
    intro s hs hsH
    exact Subsingleton.elim _ _

/--
The unrestricted version of Erdős Problem 1167 (without the condition $\gamma \geq 2$ from the
original Erdős–Hajnal list) is false. Taking $\gamma = 1$, $\kappa_0 = \aleph_1$, $\lambda =
\aleph_0$: the premise $2^{\aleph_0} \to (\aleph_1 + 1)^3_1$ holds since $2^{\aleph_0} \geq
\aleph_1$, but the conclusion $\aleph_0 \to (\aleph_1)^2_1$ fails since $\aleph_0 < \aleph_1$.
-/
@[category test, AMS 5]
theorem erdos_1167.unrestricted_is_false :
    ¬ (∀ (r : ℕ), 2 ≤ r →
    ∀ (lam : Cardinal.{u}), ℵ₀ ≤ lam →
    ∀ (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}),
      cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ (fun α => κ α + 1) →
      cardinalPartitionRel lam r γ κ) := by
  intro h
  have h1 := h 2 (le_refl _) ℵ₀ (le_refl _) 1 (fun _ => ℵ₁)
  have h2 : cardinalPartitionRel ((2 : Cardinal.{u}) ^ ℵ₀) 3 1 (fun _ => ℵ₁ + 1) := by
    rw [cardinalPartitionRel_one]
    have h3 : (ℵ₁ : Cardinal.{u}) + 1 = ℵ₁ := add_one_of_aleph0_le (aleph0_le_aleph 1)
    rw [h3]
    exact aleph_one_le_continuum
  have h3 := h1 h2
  rw [cardinalPartitionRel_one] at h3
  have h4 : (ℵ₀ : Cardinal.{u}) < ℵ₁ := aleph0_lt_aleph_one
  exact h4.2 h3
/--
The `infinite_targets` variant without the bound $\kappa_\alpha \leq \lambda$ is false.
Taking $\gamma = 1$, $\kappa_0 = 2^{\aleph_0}$, $\lambda = \aleph_0$: the premise
$2^{\aleph_0} \to (2^{\aleph_0})^3_1$ holds since $2^{\aleph_0} \leq 2^{\aleph_0}$, but the
conclusion $\aleph_0 \to (2^{\aleph_0})^2_1$ fails by Cantor's theorem.
-/
@[category test, AMS 5]
theorem erdos_1167.variants.infinite_targets_needs_bound :
    ¬ (∀ (r : ℕ), 2 ≤ r →
    ∀ (lam : Cardinal.{u}), ℵ₀ ≤ lam →
    ∀ (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}), (∀ i, ℵ₀ ≤ κ i) →
      cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ κ →
      cardinalPartitionRel lam r γ κ) := by
  intro h
  have h1 := h 2 (le_refl _) ℵ₀ (le_refl _) 1 (fun _ => (2 : Cardinal.{u}) ^ ℵ₀)
    (fun _ => (cantor ℵ₀).le)
  have h2 : cardinalPartitionRel ((2 : Cardinal.{u}) ^ ℵ₀) 3 1
      (fun _ => (2 : Cardinal.{u}) ^ ℵ₀) := by
    rw [cardinalPartitionRel_one]
  have h3 := h1 h2
  rw [cardinalPartitionRel_one] at h3
  exact (cantor ℵ₀).2 h3

end Erdos1167
