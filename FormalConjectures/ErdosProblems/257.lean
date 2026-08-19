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

/-! ### Settled infinite-support families

`erdos_257` asks whether *every* infinite support gives an irrational sum. The
four statements below say yes for four named families. They are stated in the
same shape as the open question, so they need no new definitions.

None of this is new mathematics, and no claim of novelty or priority is made.
-/

/--
If an infinite support `A` is eventually periodic -- membership of `n` and of
`n + m` agree for all `n` past some threshold `N₀` -- then for every integer
base `b ≥ 2` the sum $\sum_{n \in A} 1/(b^n-1)$ is irrational.

This is the $0$–$1$ coefficient case of Luca–Tachiya, who prove it for
arbitrary eventually periodic rational coefficients that are not eventually
zero and every integer base with $|b| > 1$
(doi:10.1142/S1793042113501121). `A.Infinite` is what stops the indicator
sequence from being eventually zero.

One settled family. It does not decide `erdos_257`, which quantifies over all
infinite supports.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/adapters/FormalConjecturesVariants.lean#L638-L647"]
theorem erdos_257.variants.eventually_periodic_support
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A)) (hA : A.Infinite) :
    Irrational (∑' n : A, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  sorry

/--
If an infinite support `A` is pairwise coprime and its reciprocals are
summable, then for every integer base `b ≥ 2` the sum
$\sum_{n \in A} 1/(b^n-1)$ is irrational.

This is Erdős, *On the Irrationality of Certain Series*, Math. Student 36
(1968), 222–226, theorem on p. 222, stated over a set rather than a sequence.
Both hypotheses are kept as Erdős states them.

One settled family. It does not decide `erdos_257`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/adapters/FormalConjecturesVariants.lean#L650-L660"]
theorem erdos_257.variants.pairwise_coprime_support
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable fun a : A => (1 : ℝ) / (a : ℕ)) :
    Irrational (∑' n : A, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  sorry

/--
For every integer base `b ≥ 2`, the sum over the positive factorials
$\sum_k 1/(b^{(k+1)!}-1)$ is irrational.

The support is indexed from $1! $ rather than $0!$, so the exponent `1` is not
repeated. The family lies in the rapidly-growing framework of Erdős–Straus,
*On the irrationality of certain Ahmes series*, J. Indian Math. Soc. 27 (1964),
129–133: all earlier denominators divide the latest one, and the next grows too
fast for the exceptional rational recurrence.

One settled family. It does not decide `erdos_257`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/adapters/FormalConjecturesVariants.lean#L663-L665"]
theorem erdos_257.variants.factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1)) := by
  sorry

/--
For every integer base `b ≥ 2`, the sum over the powers of two
$\sum_k 1/(b^{2^k}-1)$ is irrational.

This is the constant-perturbation case $b_k = -1$ of Erdős–Straus, Example 1,
pp. 132–133. Duverney later proved the stronger result that the value is
transcendental (doi:10.1017/S0305004100004783); what is recorded here is the
irrationality statement.

One settled family. It does not decide `erdos_257`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/adapters/FormalConjecturesVariants.lean#L668-L670"]
theorem erdos_257.variants.two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1)) := by
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
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/a9104f2f12aa0d4e9da8a93574b14990ed02dc2a/adapters/FormalConjecturesAdapter.lean#L119-L134"]
theorem erdos_257.variants.tsum_top :
    Irrational <| ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  sorry

/-- The finite Erdős support series at integer base `b`, summed over a finite
set of exponents. -/
def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

/--
For every nonempty finite support not containing `0`, and every integer base
`b ≥ 2` coprime to the reduced denominator of that finite sum, the
multiplicative order of `b` modulo that denominator is exactly the lcm of the
support: the period does not collapse.

This is a finite-support fact. It does not decide the infinite-set
irrationality asked about in `erdos_257`.

The coprimality hypothesis is kept: discharging it is already proved in the
linked development, but it is not a one-line Mathlib fact.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/c04870f7f7f2166f38fc4077033792ef6486f209/adapters/FormalConjecturesVariants.lean#L348-L354"]
theorem erdos_257.variants.finite_period_noncollapse
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b (finiteErdosSum F b).den) :
    orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
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
