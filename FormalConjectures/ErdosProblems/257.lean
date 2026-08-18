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

import FormalConjecturesUtil

/-!
# Erdős Problem 257

*Reference:* [erdosproblems.com/257](https://www.erdosproblems.com/257)
-/

namespace Erdos257

open scoped ENNReal

/--
Let $A\subseteq\mathbb{N}$ be an infinite set. Is
$$
\sum_{n\in A} \frac{1}{2^n - 1}
$$
irrational?
-/
@[category research open, AMS 11]
theorem erdos_257 : answer(sorry) ↔ ∀ (A : Set ℕ), A.Infinite →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry

/--
Show that
$$
\sum_{n} \frac{1}{2^n - 1} = \sum_{n} \frac{d(n)}{2^n},
$$
where $d(n)$ is the number of divisors of $n$.
-/
@[category textbook, AMS 11]
theorem erdos_257.variants.tsum_top_eq :
    ∑' n, 1 / (2 ^ n - 1 : ℝ) = ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  -- The key Lambert-series identity from Mathlib (`k = 0`):
  -- `∑' n:ℕ+, (1/2)^n / (1 - (1/2)^n) = ∑' n:ℕ+, σ 0 n * (1/2)^n`, with summands rewritten.
  have key := tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) hr 0
  have hpos : ∀ n : ℕ, 0 < n → (2 : ℝ) ≤ 2 ^ n := fun n hn ↦ by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  simp only [pow_zero, one_mul, ArithmeticFunction.sigma_zero_apply,
    show ∀ n : ℕ+, ((1 : ℝ) / 2) ^ (n : ℕ) / (1 - (1 / 2) ^ (n : ℕ))
        = 1 / (2 ^ (n : ℕ) - 1) from fun n ↦ by
      have h := hpos n n.2
      have hp : (0 : ℝ) < 2 ^ (n : ℕ) := by positivity
      have h1 : (1 : ℝ) / 2 ^ (n : ℕ) < 1 := (div_lt_one hp).2 (by linarith)
      rw [div_pow, one_pow, div_eq_div_iff (by linarith) (by linarith)]; field_simp,
    show ∀ n : ℕ+, ((n : ℕ).divisors.card : ℝ) * (1 / 2) ^ (n : ℕ)
        = (n : ℕ).divisors.card / 2 ^ (n : ℕ) from fun n ↦ by
      rw [div_pow, one_pow]; ring] at key
  -- Domination by geometric series gives `ℕ`-summability of both sides.
  have hsummL : Summable fun n : ℕ ↦ 1 / (2 ^ n - 1 : ℝ) :=
    .of_nonneg_of_le
      (fun n ↦ by have := one_le_pow₀ (one_le_two (α := ℝ)) (n := n); apply div_nonneg <;> linarith)
      (fun n ↦ by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · have h2 := hpos n h
          rw [show (2 : ℝ) * (1 / 2) ^ n = 2 / 2 ^ n by rw [div_pow, one_pow]; ring,
            div_le_div_iff₀ (by linarith) (by positivity)]; nlinarith)
      ((summable_geometric_of_norm_lt_one hr).mul_left 2)
  have hsummR : Summable fun n : ℕ ↦ (n.divisors.card : ℝ) / (2 ^ n : ℝ) :=
    .of_nonneg_of_le (fun n ↦ by positivity)
      (fun n ↦ by
        rw [pow_one, show ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n by rw [div_pow, one_pow], mul_one_div]
        gcongr; exact_mod_cast Nat.card_divisors_le_self n)
      (summable_pow_mul_geometric_of_norm_lt_one 1 hr)
  -- Bridge `ℕ+` to `ℕ`: the `n = 0` term is `0` on both sides.
  rw [← (tsum_zero_pnat_eq_tsum_nat hsummL), ← (tsum_zero_pnat_eq_tsum_nat hsummR)]
  simpa using key

/--
Show that
$$
\sum_{n} \frac{d(n)}{2^n}
$$
is irrational.

[Er48] Erdős, P., _On arithmetical properties of Lambert series_. J. Indian Math. Soc. (N.S.) (1948), 63-66.
-/
@[category research solved, AMS 11]
theorem erdos_257.variants.tsum_top :
    Irrational <| ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  sorry

/--
For a set `J` of allowed positive-exponent coordinates, the Mersenne
achievement set restricted to `J` has an exact Lebesgue-measure dichotomy: if
the forbidden coordinates form a finite set `F`, the measure is $2^{-|F|}$; if
infinitely many coordinates are forbidden, the measure is zero.

Coordinate `k` carries the term $1/(2^{k+1}-1)$. Taking `J = Set.univ`, so
`F = ∅`, gives Lebesgue measure exactly `1` for the unrestricted achievement
set of these weights.

Kovač–Tao (doi:10.1007/s10474-025-01528-0, §2.1.2 and Remark 4.1) record the
strict-tail inequality and Cantor-set structure for these exact Lambert
weights; the measure of a fast achievement set is classical (Kakeya; see
Bartoszewicz–Filipczak–Prus-Wiśniowski, doi:10.1007/s40879-020-00438-5). No
claim of mathematical novelty or priority is made.

This is a solved structural variant about the geometry of the value space. It
does not decide whether every infinite-support subseries has an irrational
sum, so `erdos_257` remains open.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/ceaee37f2df872af9e19c90f2b88d87f06fec85d/adapters/FormalConjecturesVariants.lean#L566-L573"]
theorem erdos_257.variants.support_measure_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          MeasureTheory.volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        MeasureTheory.volume (supportedMersenneAchievementSet J) = 0) := by
  sorry

/--
For a set `J` of allowed coordinates, the Mersenne digit map restricted to `J`
is injective, and its range is compact, totally disconnected and nowhere
dense; when `J` is infinite that range is perfect as well.

Coordinate `k` carries the term $1/(2^{k+1}-1)$. At `J = Set.univ` this is the
statement for the unrestricted achievement set, and the injectivity conjunct is
then unique coding: distinct supports give distinct subseries sums. `IsClosed`
is left out on purpose rather than overlooked -- the set is a compact subset of
`ℝ`, and `Perfect` carries closedness in its own first component.

Kovač–Tao (doi:10.1007/s10474-025-01528-0, Remark 4.1) prove the strict-tail
inequality for these exact weights and record both the unique coding and the
Cantor-set conclusion; the underlying achievement-set topology is classical,
going back to Kakeya. No claim of novelty or priority is made for any of it.
What is offered here is the Lean statement for arbitrary `J` -- total
disconnectedness and nowhere density descend along `⊆`, so the restricted case
costs nothing over the full one -- together with a machine-checked proof.

This is a solved structural variant about the geometry of the value space. It
does not decide whether every infinite-support subseries has an irrational sum,
so `erdos_257` remains open.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/adapters/FormalConjecturesVariants.lean#L597-L608"]
theorem erdos_257.variants.supported_achievement_set_geometry (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) ∧
      IsCompact (supportedMersenneAchievementSet J) ∧
        IsTotallyDisconnected (supportedMersenneAchievementSet J) ∧
          IsNowhereDense (supportedMersenneAchievementSet J) ∧
            (J.Infinite → Perfect (supportedMersenneAchievementSet J)) := by
  sorry

end Erdos257
