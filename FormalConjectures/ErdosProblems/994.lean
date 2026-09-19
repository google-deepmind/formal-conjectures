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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 994

*References:*
- [erdosproblems.com/994](https://www.erdosproblems.com/994)
- [Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
  (1964), 52-65.
- [Kh23] Khintchine, A., _Ein Satz über Kettenbrüche, mit arithmetischen Anwendungen_. Math. Z.
  (1923), 289--306.
- [Ma70] Marstrand, J. M., _On Khinchin's conjecture about strong uniform distribution_. Proc.
  London Math. Soc. (3) (1970), 540--556.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace Erdos994

open scoped Classical in
/-- The proportion $\frac{1}{n}\sum_{1\leq k\leq n}1_{\{k\alpha \}\in E}$ of the fractional parts
$\{k\alpha\}$, $1\leq k\leq n$, which lie in `E`. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, if Int.fract (k * α) ∈ E then (1 : ℝ) else 0) / n

/--
Let $E\subseteq (0,1)$ be a meaurable subset with Lebesgue measure $\lambda(E)$. Is it true that,
for almost all $\alpha$,
$$\lim_{n\to \infty}\frac{1}{n}\sum_{1\leq k\leq n}1_{\{k\alpha \}\in E}=\lambda(E)$$
for all $E$?

This is a conjecture of Khintchine [Kh23] (with the exceptional null set of $\alpha$ allowed to
depend on $E$). It is false, and was disproved by Marstrand [Ma70].
-/
@[category research solved, AMS 11 28]
theorem erdos_994 : answer(False) ↔
    ∀ E ⊆ Ioo (0 : ℝ) 1, MeasurableSet E →
      ∀ᵐ α : ℝ, Tendsto (visitAverage E α) atTop (nhds (volume E).toReal) := by
  sorry

/--
Read literally, with "for almost all $\alpha$" placed before "for all $E$", the statement is
trivially false: for any $\alpha$, removing the countable orbit $\{\{k\alpha\} : k\geq 1\}$ from
$(0,1)$ gives a measurable set of measure $1$ which is never visited.
-/
@[category textbook, AMS 11 28]
theorem erdos_994.variants.simultaneous :
    ¬ ∀ᵐ α : ℝ, ∀ E ⊆ Ioo (0 : ℝ) 1, MeasurableSet E →
      Tendsto (visitAverage E α) atTop (nhds (volume E).toReal) := by
  intro h
  obtain ⟨α, hα⟩ := h.exists
  set O : Set ℝ := Set.range fun k : ℕ ↦ Int.fract (((k + 1 : ℕ) : ℝ) * α) with hO_def
  have hO : volume O = 0 := (Set.countable_range _).measure_zero _
  have hE := hα (Ioo 0 1 \ O) Set.sdiff_subset
    (measurableSet_Ioo.diff (Set.countable_range _).measurableSet)
  have hvol : volume (Ioo (0 : ℝ) 1 \ O) = 1 := by
    rw [measure_sdiff_null hO, Real.volume_Ioo]
    simp
  have hzero : visitAverage (Ioo 0 1 \ O) α = fun _ ↦ 0 := by
    funext n
    unfold visitAverage
    rw [Finset.sum_eq_zero, zero_div]
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [if_neg]
    rintro ⟨-, hmem⟩
    exact hmem ⟨k - 1, by simp only [Nat.sub_add_cancel hk.1]⟩
  rw [hzero, hvol, ENNReal.toReal_one] at hE
  exact one_ne_zero (tendsto_nhds_unique hE tendsto_const_nhds)

end Erdos994
