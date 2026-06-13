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
# Erdős Problem 987

*References:*
- [erdosproblems.com/987](https://www.erdosproblems.com/987)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics, probability, and number theory II](https://arxiv.org/abs/2604.06609).
  arXiv:2604.06609 (2026).
- [Cl67] Clunie, J., On a problem of Erdős. J. London Math. Soc. (1967), 133--136.
- [Er64b] Erdős, P., Problems and results on diophantine approximations. Compositio Math. (1964),
  52-65.
- [Er65b] Erdős, P., Some remarks on number theory. Israel J. Math. (the actual reference
  cited by Clunie 1967 as [2]; the erdosproblems.com bibliography points to a different
  Erdős 1965 paper, "Some recent advances and current problems in number theory" (Lectures
  on Modern Mathematics III, 1965, 196-244), which does not appear to contain the
  exponential-sum log-bound proof).
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [Li69] Lindström, B., An inequality for $B_2$-sequences. J. Combinatorial Theory (1969), 211-212.
-/

open Filter Finset Asymptotics

namespace Erdos987

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.

## File organization

- API for the additive character `e` and the partial-sum quantity `A`.
- Single-real and simultaneous "infinitely often" Dirichlet approximation lemmas.
- Tao's L²-averaging proof of Question 1 (`parts.i`).
- Statements of Question 1, Question 2, and the historical variants
  (`sup_limsup_infty`, `log_lower_bound`, `sqrt_lower_bound`).
- Clunie's linear upper bound via the van der Corput sequence (`vdc`):
  block sum identity, partial-sum norm bounds, and the variants
  `linear_upper_bound_weak`, `linear_upper_bound_clunie`.
- The remaining historical variants (`sqrt_log_upper_bound`,
  `finite_distinct_points`).

## Status of the variants

Fully proven: `parts.i`, `sup_limsup_infty`, `log_lower_bound`, `sqrt_lower_bound`,
`finite_distinct_points`, `linear_upper_bound_weak` ($A_k \\le 2k$),
`linear_upper_bound_clunie` ($A_k \\le k+1$), plus all the supporting API lemmas.

**Clunie 1967 lemmas** (analytic core for `sqrt_lower_bound`): all fully proven:
- `clunie_lemma_one`: the Parseval inequality
  $n^2 + \\sum_{k\\ge 1} |s_k|^2 r^{2k} \\ge n^2/2 + n/(2(1-r^2))$, via Cauchy's formula on
  the disk + per-pair integral identity + algebraic tsum manipulations.
- `clunie_lemma_two_strict`: the subset construction with strict bounds
  $|s_v(\\zeta)| < 2\\sqrt v$ (middle) and $|s_v(\\zeta)| < 2c\\sqrt v$ (outer), via the
  Cesàro / block-sum extraction from the limsup definition.
- `clunie_exp_decay_contradiction`: the final numerical-contradiction step extracted into
  its own lemma (uses `Real.pow_div_factorial_le_exp` and `Real.one_sub_div_pow_le_exp_neg`).

**All `erdos_987.*` theorems are fully proven (no `sorry`).**
`linear_upper_bound` is closed via Clunie's `vdc` witness with the
`Set.Ico 0 1` hypothesis (matching the original [Cl67]/[Er64b] statement;
see the lemma's docstring on the alignment with erdosproblems.com).

The path to `sqrt_log_upper_bound` is fully assembled: the reduction
to `apssv_exists_block_bound` is proven (via `apssv_partial_sum_bound`,
`apssv_geom_envelope`, etc.). The L² variance machinery is fully closed in three
forms:
* `apssvBlockSum_variance_eq` — the formula `∫ ‖B‖² = 2^r · (1 - ‖α‖²)` where
  `α := ∫ e(k T_{w₀, P}/2^r) dη` (any reference `w₀`). Internal case-split:
  `1 ≤ k % 2^r` uses `apssv_j_factor_double_sum_mod`; `2^r ∣ k` uses the bit-flip
  symmetry argument (`apssvT_e_integral_q_eq_zero`) to derive `α = 0`.
* `apssvBlockSum_variance_bound` — `≤ 2 · 2^r`, derived as a 5-line corollary
  from `apssvBlockSum_variance_eq` + `‖α‖² ≥ 0`.
* `apssvBlockSum_variance_bound_short` — `≤ 2 · 2^(2b−r)` for `r ≤ b`.
* `apssvBlockSum_variance_bound_long` — `≤ 4π · k`, derived from
  `apssvBlockSum_variance_eq` + `apssvT_e_integral_one_sub_norm_sq_le`
  (the Step 2 linear-in-`k` Fourier coefficient bound). Strictly tighter than
  `2 · 2^r` in the long regime `k ≤ 2^(r-1)/π`.

Lemma 3.6 (finite residue reduction) is also closed in both T- and B-forms:
* `apssvT_residue_diff_bound` — `|T_{w, P} - T_{w, P mod 2^h}| ≤ 1/2^h`.
* `apssvBlockSum_residue_diff_bound` — `‖B_{P, r}(k) - B_{P mod 2^h, r}(k)‖
  ≤ 2π·k/2^h`.

The Step 7 sub-Gaussian sharpening (`apssv_exists_eta_with_block_bound` —
positive-probability union bound) is fully closed via the `Kernel.HasSubgaussianMGF`
chassis (Mathlib's conditional sub-Gaussian MGF), splitting `B = Re B + i·Im B`
and applying Hoeffding componentwise. The summation argument (`apssv_regime_split_tsum_lt_one`)
combines the M=2 (short-regime) and linear (long-regime) explicit bounds via
Tannery's dominated convergence theorem (`tendsto_tsum_of_dominated_convergence`)
on a regime-split envelope `apssvShortEnvelope ∪ apssvLongEnvelope`, with explicit
witness `C₀ = 100`.

The boundary lemma `apssv_boundary_ae` (almost-sure `apssvX η j ∈ (0, 1)`) is
fully proven: the events `apssvX η j = 0` and `apssvX η j = 1` are pushforward
preimages of singletons in the infinite Bernoulli product `∏ ℕ → Bool`, hence
have measure $\prod 1/2 = 0$ (via `infinitePi_singleton`).
-/

/- ## API for the additive character `e(x) = e^{2πi x}` -/

/-- Shorthand for the additive character $e(x) = e^{2 \pi i x}$.
(Matches `Real.fourierChar` / `𝐞` from `Mathlib/Analysis/Complex/Circle.lean`, but
kept as a local definition for readability across the many sites that use it.) -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[category API, AMS 11, simp]
lemma e_zero : e 0 = 1 := by simp [e]

@[category API, AMS 11, simp]
lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  simp

/-- $e(x)$ has unit modulus, so it lies on the unit circle. -/
@[category API, AMS 11]
lemma e_ne_zero (x : ℝ) : e x ≠ 0 := by
  intro h
  have := norm_e x
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-- $e(n) = 1$ for any integer $n$, since $e^{2\pi i n} = 1$. -/
@[category API, AMS 11, simp]
lemma e_intCast (n : ℤ) : e (n : ℝ) = 1 := by
  rw [e]
  push_cast
  rw [show ((2 * Real.pi * (n : ℂ)) * Complex.I) = (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I n

/-- $e(n) = 1$ for any natural number $n$. -/
@[category API, AMS 11, simp]
lemma e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  exact_mod_cast e_intCast (n : ℤ)

/-- $e$ is $1$-periodic: $e(x + 1) = e(x)$. -/
@[category API, AMS 11]
lemma e_add_one (x : ℝ) : e (x + 1) = e x := by
  rw [e, e]
  push_cast
  rw [show ((2 * Real.pi * ((x : ℂ) + 1)) * Complex.I) =
      ((2 * Real.pi * x) * Complex.I) + (2 * Real.pi * Complex.I) by ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- $(e(x))^k = e(kx)$ for any natural number $k$. -/
@[category API, AMS 11]
lemma e_pow_natCast (x : ℝ) (k : ℕ) : (e x) ^ k = e (k * x) := by
  rw [e, ← Complex.exp_nat_mul, e]
  congr 1
  push_cast
  ring

/-- $(e(x))^k = e(kx)$ as a complex number, viewing $k$ as a natural index. -/
@[category API, AMS 11]
lemma e_pow_eq (x : ℝ) (k : ℕ) : (e x : ℂ) ^ k = e ((k : ℝ) * x) := e_pow_natCast x k

/-- Continuity of `e` (the additive character $\theta \mapsto e^{2\pi i \theta}$). -/
@[category API, AMS 11]
lemma continuous_e : Continuous e := by
  unfold e
  refine Complex.continuous_exp.comp ?_
  exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const

/-- **Elementary orthogonality**: $\int_0^1 e(m\theta)\,d\theta = 1$ if $m = 0$ and $0$
otherwise. The base ingredient for the per-pair integral identity in Clunie's Lemma 1.

The proof uses Mathlib's `integral_exp_mul_complex` after rewriting $e(m\theta)$
as $\exp(c\theta)$ for $c = 2\pi i m$. The endpoint values cancel because $e(m) = 1$
for $m \in \mathbb{Z}$ (i.e., $\exp(2\pi i m) = 1$). -/
@[category API, AMS 11]
theorem integral_e_int_mul (m : ℤ) :
    ∫ θ in (0 : ℝ)..1, e ((m : ℝ) * θ) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [e]
  · rw [if_neg hm]
    -- Rewrite e(mθ) as exp(c·θ) where c = 2πi·m.
    set c : ℂ := 2 * Real.pi * Complex.I * (m : ℂ) with hc_def
    have hc_ne : c ≠ 0 := by
      have hm_ne : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
      simp [c, Real.pi_ne_zero, Complex.I_ne_zero, hm_ne]
    have h_eq : (fun θ : ℝ => e ((m : ℝ) * θ)) = fun θ : ℝ => Complex.exp (c * (θ : ℂ)) := by
      funext θ
      rw [e]
      congr 1
      simp [c]
      ring
    rw [h_eq, integral_exp_mul_complex hc_ne]
    -- Compute: (exp(c·1) - exp(c·0))/c = (1 - 1)/c = 0 since exp(2πim) = 1.
    have h_one : Complex.exp (c * (1 : ℝ)) = 1 := by
      simp only [Complex.ofReal_one, mul_one, c]
      rw [show (2 * Real.pi * Complex.I * (m : ℂ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I m
    have h_zero : Complex.exp (c * (0 : ℝ)) = 1 := by simp
    rw [h_one, h_zero, sub_self, zero_div]

/- ## The partial-sum quantity `A x k` -/

/--
For an infinite sequence $x_1, x_2, \ldots \in (0, 1)$, define
$$A_k = \limsup_{n \to \infty} \left\lvert \sum_{j \le n} e(k x_j) \right\rvert,$$
where $e(x) = e^{2\pi i x}$.
-/
noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

/-- **Bridge from a uniform `‖∑‖ ≤ B` to `A x k ≤ B`**: if every partial sum has norm ≤ B,
then the limsup of those norms is ≤ B (in EReal). Used to translate `sqrt_log_upper_bound`'s
finite supremum bound into the `A`-form of `parts.ii`. -/
@[category API, AMS 11]
lemma A_le_of_uniform_bound (x : ℕ → ℝ) (k : ℕ) (B : ℝ)
    (hB : ∀ n : ℕ, ‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ ≤ B) :
    A x k ≤ ((B : ℝ) : EReal) := by
  unfold A
  calc atTop.limsup (fun n : ℕ =>
        ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal))
      ≤ atTop.limsup (fun _ : ℕ => ((B : ℝ) : EReal)) :=
        Filter.limsup_le_limsup
          (Filter.Eventually.of_forall fun n => by
            exact (EReal.coe_le_coe_iff).mpr (hB n))
    _ = ((B : ℝ) : EReal) := Filter.limsup_const _

/-- For $k = 0$, every term of the exponential sum equals $1$, so the partial sums diverge and
$A_0 = \infty$. This shows that $A_k \le k$ cannot hold at $k = 0$, and explains why the
upper-bound variants below are restricted to $k \ge 1$. -/
@[category API, AMS 11]
lemma A_zero_eq_top (x : ℕ → ℝ) : A x 0 = ⊤ := by
  have key : (fun n : ℕ => (‖∑ j ∈ range n, e ((0 : ℕ) * x j)‖ : EReal)) =
      (fun n : ℕ => ((n : ℝ) : EReal)) := by
    funext n
    simp
  rw [A, key]
  exact (EReal.tendsto_coe_nhds_top_iff.mpr tendsto_natCast_atTop_atTop).limsup_eq

/-- For a constant sequence $x_j \equiv c$, every term of the exponential sum has the same
phase $e(k c)$, so the partial sum is $n \cdot e(k c)$ with absolute value $n$, giving
$A_k = \infty$ for every $k$. In particular this shows the constant case of
`finite_distinct_points`: any sequence taking only one distinct value has $A_k = \infty$ for all
$k$ (a fortiori, infinitely often). -/
@[category API, AMS 11]
lemma A_const_eq_top (c : ℝ) (k : ℕ) : A (fun _ : ℕ => c) k = ⊤ := by
  have key : (fun n : ℕ => (‖∑ j ∈ range n, e ((k : ℝ) * c)‖ : EReal)) =
      (fun n : ℕ => ((n : ℝ) : EReal)) := by
    funext n
    simp [Finset.sum_const, Finset.card_range]
  rw [A, key]
  exact (EReal.tendsto_coe_nhds_top_iff.mpr tendsto_natCast_atTop_atTop).limsup_eq

/- ## Single-real ∞-often Dirichlet approximation

The lemmas in this section establish that for any real $\xi$ and any $\varepsilon > 0$,
there are infinitely many positive natural $k$ with $|k \xi - \mathrm{round}(k \xi)| < \varepsilon$.
The proof splits into the rational case (multiples of the denominator) and the irrational case
(via Mathlib's `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` plus an
unbounded-denominators argument). -/

/-- **Infinitely-often Dirichlet (rational case).** For any rational $q$, there are infinitely
many positive natural $k$ with $k q \in \mathbb{Z}$ (in particular,
$|k q - \mathrm{round}(k q)| = 0 < \varepsilon$ for any $\varepsilon > 0$). The witnesses are
multiples of the denominator. -/
@[category API, AMS 11]
theorem _root_.Rat.exists_freq_natCast_mul_isInt (q : ℚ) :
    ∃ᶠ k : ℕ in atTop, ((k : ℝ) * (q : ℝ)) = round ((k : ℝ) * (q : ℝ)) := by
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨q.den * (N + 1), ?_, ?_⟩
  · have hpos : 1 ≤ q.den := q.pos
    calc N ≤ N + 1 := Nat.le_succ N
      _ ≤ q.den * (N + 1) := Nat.le_mul_of_pos_left _ hpos
  · -- (q.den * (N+1)) * q = (N+1) * q.num ∈ ℤ.
    have hd_ne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
    have heq : ((q.den * (N + 1) : ℕ) : ℝ) * (q : ℝ) = (((N + 1 : ℕ) * q.num : ℤ) : ℝ) := by
      push_cast
      rw [show (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) from by
        exact_mod_cast (Rat.num_div_den q).symm]
      field_simp
    rw [heq, round_intCast]

/-- **Bound from rational approximation.** If $|\xi - q| < 1/q.\mathrm{den}^2$, then
$|q.\mathrm{den} \cdot \xi - \mathrm{round}(q.\mathrm{den} \cdot \xi)| < 1/q.\mathrm{den}$.

Uses Mathlib's `round_le` to bound `|x - round x|` by `|x - q.num|`, then unpacks
`|q.den · ξ - q.num| = q.den · |ξ - q|`. -/
@[category API, AMS 11]
theorem _root_.Real.abs_natCast_den_mul_sub_round_lt_of_rat_approx
    {ξ : ℝ} {q : ℚ} (h : |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2) :
    |(q.den : ℝ) * ξ - round ((q.den : ℝ) * ξ)| < 1 / (q.den : ℝ) := by
  have hd_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  refine lt_of_le_of_lt (round_le _ q.num) ?_
  -- |q.den * ξ - q.num| = q.den * |ξ - q|, then bound by q.den * 1/q.den² = 1/q.den.
  have heq : (q.den : ℝ) * ξ - (q.num : ℝ) = (q.den : ℝ) * (ξ - (q : ℝ)) := by
    rw [show (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) from by
      exact_mod_cast (Rat.num_div_den q).symm]
    field_simp
  rw [heq, abs_mul, abs_of_pos hd_pos]
  calc (q.den : ℝ) * |ξ - (q : ℝ)|
      < (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) := mul_lt_mul_of_pos_left h hd_pos
    _ = 1 / (q.den : ℝ) := by field_simp

/-- **Finite fiber.** For fixed positive denominator $d$ and any $\xi : \mathbb{R}$, the set of
rationals with denominator exactly $d$ and within $1/d^2$ of $\xi$ is finite. The proof is by
showing that the numerator of any such $q$ lies in the integer interval
$[\lceil d \xi - 1/d\rceil, \lfloor d \xi + 1/d\rfloor]$, and that $q$ is determined by its
numerator (since the denominator is fixed). -/
@[category API, AMS 11]
theorem _root_.Rat.finite_with_den_eq_of_close (ξ : ℝ) {d : ℕ} (hd : 0 < d) :
    {q : ℚ | q.den = d ∧ |ξ - (q : ℝ)| < 1 / (d : ℝ) ^ 2}.Finite := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  -- Embed the set into the image of Icc ⌈d*ξ - 1/d⌉ ⌊d*ξ + 1/d⌋ under n ↦ n/d.
  apply Set.Finite.subset
    (((Finset.Icc ⌈(d : ℝ) * ξ - 1 / d⌉ ⌊(d : ℝ) * ξ + 1 / d⌋).image
      (fun n : ℤ => ((n : ℚ) / (d : ℚ)))) : Finset ℚ).finite_toSet
  intro q ⟨hq_den, hq_close⟩
  simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc]
  -- Step 1: q.num : ℝ = q * d (uses q = q.num/q.den and q.den = d).
  have heq : (q.num : ℝ) = (q : ℝ) * d := by
    rw [show (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) from by
      exact_mod_cast (Rat.num_div_den q).symm, hq_den]
    field_simp
  -- Step 2: |d*ξ - q.num| < 1/d (multiply |ξ - q| < 1/d² by d).
  have habs : |(d : ℝ) * ξ - (q.num : ℝ)| < 1 / (d : ℝ) := by
    have hmul : (d : ℝ) * |ξ - (q : ℝ)| < (d : ℝ) * (1 / (d : ℝ) ^ 2) :=
      mul_lt_mul_of_pos_left hq_close hd_pos
    have hsimp : (d : ℝ) * (1 / (d : ℝ) ^ 2) = 1 / (d : ℝ) := by field_simp
    rw [show (d : ℝ) * ξ - (q.num : ℝ) = (d : ℝ) * (ξ - (q : ℝ)) from by
      rw [heq]; ring]
    rw [abs_mul, abs_of_pos hd_pos]
    linarith
  -- Step 3: Extract bounds q.num > d*ξ - 1/d and q.num < d*ξ + 1/d.
  rw [abs_sub_lt_iff] at habs
  obtain ⟨h1, h2⟩ := habs
  -- Step 4: Construct the witness.
  refine ⟨q.num, ⟨?_, ?_⟩, ?_⟩
  · -- ⌈d*ξ - 1/d⌉ ≤ q.num
    rw [Int.ceil_le]
    linarith
  · -- q.num ≤ ⌊d*ξ + 1/d⌋
    rw [Int.le_floor]
    linarith
  · -- (q.num : ℚ) / (d : ℚ) = q
    rw [show ((d : ℕ) : ℚ) = (q.den : ℚ) from by rw [hq_den]]
    exact_mod_cast Rat.num_div_den q

/-- **Unbounded denominators of good approximations.** For irrational $\xi$, the denominators
of "good" rational approximations $\{q : \mathbb{Q} \mid |\xi - q| < 1/q.\mathrm{den}^2\}$ are
unbounded: for every $M$, there exists such $q$ with $q.\mathrm{den} \ge M$.

The proof is by contradiction: if all denominators are $< M$, then the (infinite) set of good
approximations is contained in a finite union of finite fibers
(via `Rat.finite_with_den_eq_of_close`), which gives a finite set — contradicting
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`. -/
@[category API, AMS 11]
theorem _root_.Real.exists_unbounded_den_rat_approx_of_irrational
    {ξ : ℝ} (hξ : Irrational ξ) (M : ℕ) :
    ∃ q : ℚ, |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ M ≤ q.den := by
  by_contra hbdd
  push_neg at hbdd
  apply Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ
  apply Set.Finite.subset
    (Set.Finite.biUnion (Finset.Ico 1 M).finite_toSet (fun d hd => by
      simp only [Finset.coe_Ico, Set.mem_Ico] at hd
      exact Rat.finite_with_den_eq_of_close ξ hd.1))
  intro q hq
  simp only [Set.mem_iUnion, Finset.coe_Ico, Set.mem_Ico, exists_prop]
  refine ⟨q.den, ⟨q.pos, hbdd q hq⟩, rfl, ?_⟩
  convert hq

/-- **Infinitely-often Dirichlet (irrational case).** For irrational $\xi$ and any
$\varepsilon > 0$, there are infinitely many positive natural $k$ with
$|k \xi - \mathrm{round}(k \xi)| < \varepsilon$. The witnesses are denominators of "good"
rational approximations to $\xi$. -/
@[category API, AMS 11]
theorem _root_.Real.exists_freq_natCast_mul_sub_round_lt_of_irrational
    {ξ : ℝ} (hξ : Irrational ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k : ℕ in atTop, |(k : ℝ) * ξ - round ((k : ℝ) * ξ)| < ε := by
  rw [Filter.frequently_atTop]
  intro N
  -- Pick threshold M = max(N, ⌈1/ε⌉₊).
  set M := max N ⌈1 / ε⌉₊ with hM_def
  have hMN : N ≤ M := le_max_left _ _
  have hMε : (1 / ε : ℝ) ≤ M :=
    calc (1 / ε : ℝ) ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
      _ ≤ (M : ℝ) := by exact_mod_cast Nat.le_max_right _ _
  -- Get a "good" rational q with q.den ≥ M.
  obtain ⟨q, hq_close, hq_den⟩ := Real.exists_unbounded_den_rat_approx_of_irrational hξ M
  have hq_den_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  refine ⟨q.den, hMN.trans hq_den, ?_⟩
  refine lt_of_lt_of_le (Real.abs_natCast_den_mul_sub_round_lt_of_rat_approx hq_close) ?_
  -- 1/q.den ≤ ε.
  rw [div_le_iff₀ hq_den_pos]
  rw [div_le_iff₀ hε] at hMε
  rw [mul_comm]
  calc (1 : ℝ) ≤ M * ε := hMε
    _ ≤ q.den * ε := by
      apply mul_le_mul_of_nonneg_right _ hε.le
      exact_mod_cast hq_den

/-- **Infinitely-often Dirichlet (full statement).** For any real $\xi$ and any
$\varepsilon > 0$, there are infinitely many positive natural $k$ with
$|k \xi - \mathrm{round}(k \xi)| < \varepsilon$. The rational and irrational cases are handled
separately by `Rat.exists_freq_natCast_mul_isInt` and
`Real.exists_freq_natCast_mul_sub_round_lt_of_irrational`. -/
@[category API, AMS 11]
theorem _root_.Real.exists_freq_natCast_mul_sub_round_lt
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k : ℕ in atTop, |(k : ℝ) * ξ - round ((k : ℝ) * ξ)| < ε := by
  by_cases hξ : Irrational ξ
  · exact Real.exists_freq_natCast_mul_sub_round_lt_of_irrational hξ hε
  · rw [Irrational, not_not] at hξ
    obtain ⟨q, rfl⟩ := hξ
    refine (Rat.exists_freq_natCast_mul_isInt q).mono fun k hk => ?_
    rw [hk, round_intCast, sub_self, abs_zero]
    exact hε

/- ## Simultaneous ∞-often Dirichlet approximation

For a finite set $Y$ of reals and any $\varepsilon > 0$, there are infinitely many positive
natural $k$ with $|k y - \mathrm{round}(k y)| < \varepsilon$ for *every* $y \in Y$
simultaneously. The rational case is direct (lcm of denominators); the general case uses
Bolzano-Weierstrass on `AddCircle 1`. -/

/-- **Simultaneous Dirichlet, rational case.** For a finite set $Y$ of rationals, infinitely
many positive natural $k$ satisfy $k \cdot q \in \mathbb{Z}$ for *every* $q \in Y$
simultaneously. The witnesses are multiples of $L = \mathrm{lcm}\{q.\mathrm{den} : q \in Y\}$. -/
@[category API, AMS 11]
theorem _root_.Finset.exists_freq_natCast_mul_isInt_of_rat (Y : Finset ℚ) :
    ∃ᶠ k : ℕ in atTop, ∀ q ∈ Y, ((k : ℝ) * (q : ℝ)) = round ((k : ℝ) * (q : ℝ)) := by
  rw [Filter.frequently_atTop]
  intro N
  let L : ℕ := Y.lcm (·.den)
  have hL_pos : 1 ≤ L := by
    rw [show (1 : ℕ) = (1 : ℕ).succ - 1 from rfl]
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [L, Finset.lcm]
      -- Y.fold lcm 1 (·.den) ≠ 0 since 1 ≠ 0 and lcm preserves ≠ 0.
      -- Actually, Multiset lcm: lcm of (s.1.map (·.den)) ≠ 0 since each q.den ≠ 0 and 1 ≠ 0.
      intro h
      have : (Y.lcm (·.den) : ℕ) = 0 := h
      rw [Finset.lcm_eq_zero_iff] at this
      obtain ⟨q, hq, hq_zero⟩ := this
      exact (q.pos.ne' hq_zero))
  refine ⟨L * (N + 1), ?_, ?_⟩
  · calc N ≤ N + 1 := Nat.le_succ _
      _ = 1 * (N + 1) := by ring
      _ ≤ L * (N + 1) := Nat.mul_le_mul_right _ hL_pos
  · intro q hq
    -- q.den ∣ L, so write L = q.den * c.
    have hden_dvd : q.den ∣ L := Finset.dvd_lcm hq
    obtain ⟨c, hc⟩ := hden_dvd
    -- Show (L * (N+1)) * q = ((N+1) * c * q.num : ℤ).
    have hd_ne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
    have hkq : ((L * (N + 1) : ℕ) : ℝ) * (q : ℝ) = (((N + 1 : ℕ) * c * q.num : ℤ) : ℝ) := by
      rw [show L = q.den * c from hc]
      push_cast
      rw [show (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) from by
        exact_mod_cast (Rat.num_div_den q).symm]
      field_simp
    rw [hkq, round_intCast]

/-- **Triangle inequality for round-distance on differences.** For any reals $a, b$,
$|(a - b) - \mathrm{round}(a - b)| \le |a - \mathrm{round}(a)| + |b - \mathrm{round}(b)|$.
Used in the difference-step of the simultaneous Dirichlet induction. -/
@[category API, AMS 11]
lemma _root_.Real.abs_sub_round_sub_le (a b : ℝ) :
    |(a - b) - round (a - b)| ≤ |a - round a| + |b - round b| := by
  refine le_trans (round_le _ (round a - round b)) ?_
  push_cast
  rw [show a - b - (↑(round a) - ↑(round b)) = (a - round a) - (b - round b) from by ring]
  exact abs_sub _ _

/-- **Quantitative simultaneous Dirichlet approximation.**

For any $n$ real numbers $y_1, \ldots, y_n$ and any positive integer $Q$, there is a
positive natural $k \le Q^n$ such that $|k y_i - \mathrm{round}(k y_i)| < 1/Q$ for all
$i$ simultaneously.

This is the standard pigeonhole proof of simultaneous Dirichlet approximation.
Considering the $Q^n + 1$ points $(\{m y_1\}, \ldots, \{m y_n\}) \in [0,1)^n$ for
$m = 0, 1, \ldots, Q^n$ and dividing $[0,1)^n$ into $Q^n$ boxes of side $1/Q$, by
pigeonhole two distinct $m_1 < m_2$ share a box, and $k := m_2 - m_1$ works.

Used in `log_lower_bound` to derive the $A_k \gg \log k$ bound: with $Q = 7$ and
$y_i = x_{rn+i}$, the bound gives a $k \le 7^n$ such that $\mathrm{Re}(z_j^k) > 1/2$
for the relevant block, hence $|S^{(r)}_n| > n/2$ and $A_k \gg n \gg \log k$. -/
@[category API, AMS 11]
theorem _root_.Real.exists_simul_dirichlet
    {n : ℕ} (y : Fin n → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ k : ℕ, 0 < k ∧ k ≤ Q ^ n ∧
      ∀ i, |(k : ℝ) * y i - round ((k : ℝ) * y i)| < 1 / Q := by
  have hQR_pos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h_boxIdx_lt : ∀ (m : ℕ) (i : Fin n),
      (⌊(Q : ℝ) * Int.fract ((m : ℝ) * y i)⌋).toNat < Q := by
    intro m i
    have hfract_lt : Int.fract ((m : ℝ) * y i) < 1 := Int.fract_lt_one _
    have hfract_nn : 0 ≤ Int.fract ((m : ℝ) * y i) := Int.fract_nonneg _
    have h_lt : (Q : ℝ) * Int.fract ((m : ℝ) * y i) < Q :=
      (mul_lt_mul_of_pos_left hfract_lt hQR_pos).trans_eq (mul_one _)
    have h_floor_lt : ⌊(Q : ℝ) * Int.fract ((m : ℝ) * y i)⌋ < (Q : ℤ) :=
      Int.floor_lt.mpr (by exact_mod_cast h_lt)
    have h_nn : (0 : ℤ) ≤ ⌊(Q : ℝ) * Int.fract ((m : ℝ) * y i)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hQR_pos.le hfract_nn)
    exact (Int.toNat_lt h_nn).mpr h_floor_lt
  -- Box function and pigeonhole.
  set box : ℕ → Fin n → Fin Q := fun m i =>
    ⟨(⌊(Q : ℝ) * Int.fract ((m : ℝ) * y i)⌋).toNat, h_boxIdx_lt m i⟩ with hbox_def
  have hcard_codomain : Fintype.card (Fin n → Fin Q) = Q ^ n := by
    simp [Fintype.card_pi, Fintype.card_fin]
  let S := Finset.range (Q ^ n + 1)
  have h_maps_to : ∀ m ∈ S, box m ∈ (Finset.univ : Finset (Fin n → Fin Q)) :=
    fun m _ => Finset.mem_univ _
  have hcard_lt : (Finset.univ : Finset (Fin n → Fin Q)).card < S.card := by
    rw [Finset.card_univ, hcard_codomain, Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt h_maps_to
  -- Helper to turn box-equality into a key fract bound.
  have h_S_le : ∀ m ∈ S, m ≤ Q ^ n := by
    intro m hm; rw [Finset.mem_range] at hm; omega
  -- For any m₁ < m₂ in S with box m₁ = box m₂, the witness k = m₂ - m₁ works.
  suffices h_main : ∀ m₁ m₂ : ℕ, m₁ ∈ S → m₂ ∈ S → m₁ < m₂ → box m₁ = box m₂ →
      ∃ k : ℕ, 0 < k ∧ k ≤ Q ^ n ∧
        ∀ i, |(k : ℝ) * y i - round ((k : ℝ) * y i)| < 1 / Q by
    rcases lt_or_gt_of_ne hne with h | h
    · exact h_main a b ha hb h heq
    · exact h_main b a hb ha h heq.symm
  intro m₁ m₂ hm₁ hm₂ h_lt heq'
  refine ⟨m₂ - m₁, by omega, by have := h_S_le m₂ hm₂; omega, ?_⟩
  intro i
  have hbox_val :
      (⌊(Q : ℝ) * Int.fract ((m₁ : ℝ) * y i)⌋).toNat =
      (⌊(Q : ℝ) * Int.fract ((m₂ : ℝ) * y i)⌋).toNat := by
    have h := Fin.val_eq_of_eq (congr_fun heq' i)
    -- Unfold the box definition.
    show (box m₁ i).val = (box m₂ i).val
    exact h
  have hfloor_eq :
      ⌊(Q : ℝ) * Int.fract ((m₂ : ℝ) * y i)⌋ =
      ⌊(Q : ℝ) * Int.fract ((m₁ : ℝ) * y i)⌋ := by
    have h_nn₁ : (0 : ℤ) ≤ ⌊(Q : ℝ) * Int.fract ((m₁ : ℝ) * y i)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hQR_pos.le (Int.fract_nonneg _))
    have h_nn₂ : (0 : ℤ) ≤ ⌊(Q : ℝ) * Int.fract ((m₂ : ℝ) * y i)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hQR_pos.le (Int.fract_nonneg _))
    have h₁ := Int.toNat_of_nonneg h_nn₁
    have h₂ := Int.toNat_of_nonneg h_nn₂
    omega
  have hfract_diff_lt :
      |Int.fract ((m₂ : ℝ) * y i) - Int.fract ((m₁ : ℝ) * y i)| < 1 / Q := by
    have h_diff_lt :
        |((Q : ℝ) * Int.fract ((m₂ : ℝ) * y i)) -
         ((Q : ℝ) * Int.fract ((m₁ : ℝ) * y i))| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hfloor_eq
    have h_factored :
        (Q : ℝ) * Int.fract ((m₂ : ℝ) * y i) - (Q : ℝ) * Int.fract ((m₁ : ℝ) * y i) =
        (Q : ℝ) * (Int.fract ((m₂ : ℝ) * y i) - Int.fract ((m₁ : ℝ) * y i)) := by ring
    rw [h_factored, abs_mul, abs_of_pos hQR_pos] at h_diff_lt
    rw [div_eq_inv_mul, lt_inv_mul_iff₀ hQR_pos]
    linarith
  have hk_yi_eq :
      ((m₂ - m₁ : ℕ) : ℝ) * y i -
        ((⌊(m₂ : ℝ) * y i⌋ - ⌊(m₁ : ℝ) * y i⌋ : ℤ) : ℝ) =
      Int.fract ((m₂ : ℝ) * y i) - Int.fract ((m₁ : ℝ) * y i) := by
    have hk_cast : ((m₂ - m₁ : ℕ) : ℝ) = (m₂ : ℝ) - (m₁ : ℝ) := by
      rw [Nat.cast_sub h_lt.le]
    have h_eq₁ : Int.fract ((m₁ : ℝ) * y i) = (m₁ : ℝ) * y i - ⌊(m₁ : ℝ) * y i⌋ := by
      rw [Int.fract]
    have h_eq₂ : Int.fract ((m₂ : ℝ) * y i) = (m₂ : ℝ) * y i - ⌊(m₂ : ℝ) * y i⌋ := by
      rw [Int.fract]
    rw [hk_cast, h_eq₁, h_eq₂]; push_cast; ring
  have h_close_int :
      |((m₂ - m₁ : ℕ) : ℝ) * y i -
        ((⌊(m₂ : ℝ) * y i⌋ - ⌊(m₁ : ℝ) * y i⌋ : ℤ) : ℝ)| < 1 / Q := by
    rw [hk_yi_eq]; exact hfract_diff_lt
  exact lt_of_le_of_lt (round_le _ _) h_close_int

/-- **Simultaneous ∃ᶠ Dirichlet, general case.** For any finite set of reals $Y$ and
$\varepsilon > 0$, there are infinitely many positive natural $k$ with
$|k y - \mathrm{round}(k y)| < \varepsilon$ for all $y \in Y$ simultaneously.

The proof is by induction on $|Y|$.

Inductive step: from $\exists^\infty k, \forall y \in Y', |k y - \mathrm{round}(k y)|
< \varepsilon/2$, extract a strictly monotone witness sequence $\varphi$. Apply
`CompactSpace.tendsto_subseq` on `AddCircle (1 : ℝ)` to extract $\psi$ along which
$(\varphi(\psi(n)) \cdot y_0)$ converges to some $\alpha$. For each lower threshold $N$,
pick $J_0$ in the eventually-$\varepsilon/4$-close range and $m_2 > J_0$ with
$\varphi(\psi(m_2)) \ge \varphi(\psi(J_0)) + N$ (possible since $\varphi \circ \psi
\to \infty$). The witness $k = \varphi(\psi(m_2)) - \varphi(\psi(J_0))$ then satisfies:
- $k \ge N$;
- $|k y - \mathrm{round}(k y)| < \varepsilon$ for $y \in Y'$
  (via `Real.abs_sub_round_sub_le`);
- $|k y_0 - \mathrm{round}(k y_0)| < \varepsilon/2 < \varepsilon$
  (using `UnitAddCircle.norm_eq` and the triangle inequality on `AddCircle (1 : ℝ)`). -/
@[category API, AMS 11]
theorem _root_.Finset.exists_freq_natCast_mul_sub_round_lt
    (Y : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k : ℕ in atTop, ∀ y ∈ Y, |(k : ℝ) * y - round ((k : ℝ) * y)| < ε := by
  -- Strengthen statement to allow IH application with smaller ε.
  suffices h : ∀ Y : Finset ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ k : ℕ in atTop, ∀ y ∈ Y, |(k : ℝ) * y - round ((k : ℝ) * y)| < ε by
    exact h Y ε hε
  clear hε ε Y
  intro Y
  induction Y using Finset.induction_on with
  | empty =>
    intro ε _
    rw [Filter.frequently_atTop]
    intro N
    exact ⟨N, le_refl N, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert y₀ Y' hy₀_notin ih =>
    intro ε hε
    have hε_half : 0 < ε / 2 := half_pos hε
    have hε_quarter : 0 < ε / 4 := by linarith
    have ih_half := ih (ε / 2) hε_half
    haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
    rw [Filter.frequently_atTop]
    intro N
    -- 1. Extract strictly monotone witness sequence for IH (with ε/2 bound).
    obtain ⟨φ, hφ_mono, hφ_bd⟩ := extraction_of_frequently_atTop ih_half
    -- 2. Apply compactness of AddCircle (1 : ℝ) to (φ n) y₀ ∈ AddCircle (1 : ℝ).
    obtain ⟨α, ψ, hψ_mono, hψ_tendsto⟩ :=
      CompactSpace.tendsto_subseq
        (fun n => (↑((φ n : ℝ) * y₀) : AddCircle (1 : ℝ)))
    -- 3. Eventually dist(φ(ψ n) * y₀, α) < ε/4.
    have heven : ∀ᶠ n in atTop,
        dist (↑((φ (ψ n) : ℝ) * y₀) : AddCircle (1 : ℝ)) α < ε / 4 :=
      hψ_tendsto.eventually (Metric.ball_mem_nhds α hε_quarter)
    rw [Filter.eventually_atTop] at heven
    obtain ⟨J₀, hJ₀⟩ := heven
    -- 4. Find m₂ > J₀ with φ(ψ m₂) ≥ φ(ψ J₀) + N.
    have hφψ_atTop : Tendsto (φ ∘ ψ) atTop atTop := (hφ_mono.comp hψ_mono).tendsto_atTop
    obtain ⟨m₂, hm₂_ge, hm₂_big⟩ : ∃ m, J₀ + 1 ≤ m ∧ φ (ψ J₀) + N ≤ φ (ψ m) := by
      have h := hφψ_atTop.eventually_ge_atTop (φ (ψ J₀) + N)
      rw [Filter.eventually_atTop] at h
      obtain ⟨M, hM⟩ := h
      exact ⟨max M (J₀ + 1), le_max_right _ _, hM _ (le_max_left _ _)⟩
    have hm₂_J₀ : J₀ ≤ m₂ := le_of_lt (Nat.lt_of_succ_le hm₂_ge)
    have hφψ_lt : φ (ψ J₀) ≤ φ (ψ m₂) := by
      have := (hφ_mono.comp hψ_mono) (Nat.lt_of_succ_le hm₂_ge)
      omega
    -- 5. The witness: k = φ(ψ m₂) - φ(ψ J₀). It satisfies k ≥ N.
    refine ⟨φ (ψ m₂) - φ (ψ J₀), ?_, ?_⟩
    · omega
    -- 6. Verify all bounds.
    intro y hy
    rw [Finset.mem_insert] at hy
    -- Cast of subtraction: (φ(ψ m₂) - φ(ψ J₀) : ℕ → ℝ) = (φ(ψ m₂) : ℝ) - (φ(ψ J₀) : ℝ).
    have hcast : ((φ (ψ m₂) - φ (ψ J₀) : ℕ) : ℝ) = (φ (ψ m₂) : ℝ) - (φ (ψ J₀) : ℝ) :=
      Nat.cast_sub hφψ_lt
    rw [hcast,
        show ((φ (ψ m₂) : ℝ) - (φ (ψ J₀) : ℝ)) * y =
            (φ (ψ m₂) : ℝ) * y - (φ (ψ J₀) : ℝ) * y from by ring]
    rcases hy with rfl | hy
    · -- Case y = y₀: bound from triangle in AddCircle (1 : ℝ).
      -- Bound by ε/2 via UnitAddCircle.norm_eq + triangle in AddCircle.
      have hnorm : ‖(↑((φ (ψ m₂) : ℝ) * y - (φ (ψ J₀) : ℝ) * y) : AddCircle (1 : ℝ))‖ < ε / 2 := by
        rw [show ((φ (ψ m₂) : ℝ) * y - (φ (ψ J₀) : ℝ) * y : ℝ) =
            ((φ (ψ m₂) : ℝ) * y) - ((φ (ψ J₀) : ℝ) * y) from rfl,
          AddCircle.coe_sub, ← dist_eq_norm]
        calc dist (↑((φ (ψ m₂) : ℝ) * y) : AddCircle (1 : ℝ))
                  (↑((φ (ψ J₀) : ℝ) * y) : AddCircle (1 : ℝ))
            ≤ dist (↑((φ (ψ m₂) : ℝ) * y) : AddCircle (1 : ℝ)) α
              + dist α (↑((φ (ψ J₀) : ℝ) * y) : AddCircle (1 : ℝ)) := dist_triangle _ _ _
          _ < ε / 4 + ε / 4 := by
              apply add_lt_add (hJ₀ m₂ hm₂_J₀)
              rw [dist_comm]; exact hJ₀ J₀ (le_refl _)
          _ = ε / 2 := by ring
      rw [UnitAddCircle.norm_eq] at hnorm
      linarith
    · -- Case y ∈ Y': bound via Real.abs_sub_round_sub_le from two ε/2 bounds.
      refine lt_of_le_of_lt (Real.abs_sub_round_sub_le _ _) ?_
      have h1 := hφ_bd (ψ m₂) y hy
      have h2 := hφ_bd (ψ J₀) y hy
      linarith



/-
## Tao's proof of Question 1, factored into reusable pieces

Tao's solution to Q1 of Erdős Problem 987 (adapted from
[teorth/analysis](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_987.lean))
splits naturally into:

1. `Circle.exists_shift_uniform_bound` — a "shift" argument: from an eventually-bounded
   limsup hypothesis, construct a shifted sequence whose partial sums are bounded
   uniformly in $n$ (no exception for small $n$).
2. `Circle.l2_averaging_bound` — the $L^2$-averaging key inequality: for sequences on
   the unit circle whose partial sums are uniformly bounded, an arithmetic inequality
   relating $n$, $K$, and $k_0$ holds.
3. `tao_circle` — the main theorem, which combines (1) and (2) with a final arithmetic
   contradiction step.

These pieces should be reusable (e.g. for proving the harder `sqrt_lower_bound` variant).
-/

/-- **Shift lemma.** Suppose that for each $k \ge k_0$, the partial sums
$\|\sum_{j < n} z_j^k\|$ are eventually less than $C + 1$ (i.e. for $n$ large enough,
depending on $k$). Then for any cutoff $K$ there exists a single shift $N_0$ such that
the *shifted* sequence $w_j := z_{N_0 + j}$ satisfies
$\|\sum_{j < n} w_j^k\| < 2(C + 1)$ for **all** $n \ge 0$ and all $k \in [k_0, K]$,
with no exception for small $n$. -/
@[category API, AMS 11]
theorem Circle.exists_shift_uniform_bound (z : ℕ → Circle) (C : ℝ) (k₀ : ℕ)
    (hN : ∀ k ≥ k₀, ∃ N, ∀ n ≥ N, ‖∑ j ∈ range n, ((z j) ^ k : ℂ)‖ < C + 1) (K : ℕ) :
    ∃ w : ℕ → Circle, ∀ n, ∀ k ≤ K, k ≥ k₀ →
      ‖∑ j ∈ range n, ((w j) ^ k : ℂ)‖ < 2 * (C + 1) := by
  choose N hN using hN
  let N₀ := ∑ k ≤ K, if h : k ≥ k₀ then N k h else 0
  refine ⟨fun j ↦ z (N₀ + j), ?_⟩
  simp only
  intro n k hk hk₀
  have hN₀ : N k hk₀ ≤ N₀ := by
    convert single_le_sum (a := k) _ _ <;> try simp [hk, hk₀]
    infer_instance
  calc
    _ = ‖∑ j ∈ range (N₀ + n), ((z j) ^ k : ℂ) - ∑ j ∈ range N₀, ((z j) ^ k : ℂ)‖ := by
      rw [sum_range_add_sub_sum_range]
    _ ≤ ‖∑ j ∈ range (N₀ + n), ((z j) ^ k : ℂ)‖ + ‖∑ j ∈ range N₀, ((z j) ^ k : ℂ)‖ :=
      norm_sub_le _ _
    _ < (C + 1) + (C + 1) := by gcongr <;> apply hN <;> linarith
    _ = _ := by ring

open Complex in
/-- **$L^2$-averaging key inequality.** If $w : \mathbb{N} \to \mathrm{Circle}$ satisfies
$\|\sum_{j < n} w_j^k\| < C'$ uniformly in $n$ for all $k \in [k_0, K]$, then
$$n \cdot K^2 \;\le\; K^2 \cdot (C')^2 \;+\; K \cdot (2 k_0 \cdot n^2).$$

The proof expands $n \cdot K^2$ as a double sum over diagonal pairs $(j, j')$ in
$\{0, \ldots, n-1\}$, transposes to a sum over $(k, k')$, and then bounds each
off-diagonal contribution either by the hypothesis (when $|k - k'| \ge k_0$) or by
the trivial $n^2$ bound (when $|k - k'| < k_0$, of which there are at most $2k_0$
values per $k$). -/
@[category API, AMS 11]
theorem Circle.l2_averaging_bound {C' : ℝ} (w : ℕ → Circle) (k₀ K n : ℕ)
    (hw : ∀ n, ∀ k ≤ K, k ≥ k₀ → ‖∑ j ∈ range n, ((w j) ^ k : ℂ)‖ < C') :
    (n : ℝ) * K ^ 2 ≤ K ^ 2 * (C') ^ 2 + K * ((2 * k₀) * n ^ 2) := by
  calc
    _ = ∑ _ ∈ range n, (K : ℝ) ^ 2 := by simp
    _ = ∑ j ∈ range n, ∑ j' ∈ range n, (if j = j' then (K : ℝ) ^ 2 else 0) := by
      apply sum_congr rfl; aesop
    _ ≤ ∑ j ∈ range n, ∑ j' ∈ range n,
          ‖∑ k ∈ range K, (((w j) ^ k : ℂ) / ((w j') ^ k : ℂ))‖ ^ 2 := by
      apply sum_le_sum; intro j _; apply sum_le_sum; intro j' _
      split_ifs with h <;> simp [h]
    _ = ∑ k ∈ range K, ∑ k' ∈ range K,
          ‖∑ j ∈ range n, (((w j) ^ k : ℂ) / ((w j) ^ (k') : ℂ))‖ ^ 2 := by
      simp_rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_inj, Complex.ofReal_sum,
        Complex.normSq_eq_conj_mul_self, map_sum, sum_mul_sum,
        sum_comm (s := range n) (t := range K)]
      apply sum_congr rfl; intro k _; apply sum_congr rfl; intro k' _
      apply sum_congr rfl; intro j _; apply sum_congr rfl; intro j' _
      simp only [map_pow, map_div₀]
      field_simp
      ring_nf
      simp [← Circle.coe_inv_eq_conj]
    _ ≤ ∑ k ∈ range K, ∑ k' ∈ range K,
          ((C') ^ 2 + (if k < k' + k₀ ∧ k' < k + k₀ then (n : ℝ) ^ 2 else 0)) := by
      apply sum_le_sum; intro k hk; apply sum_le_sum; intro k' hk'; simp at hk hk'
      split_ifs with h
      · calc
          _ ≤ (n : ℝ) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity); convert norm_sum_le _ _; simp
          _ ≤ _ := by simp; nlinarith
      simp; apply pow_le_pow_left₀ (by positivity)
      replace h : (∃ l ≥ k₀, k = k' + l) ∨ (∃ l ≥ k₀, k' = k + l) := by
        have : k' + k₀ ≤ k ∨ k + k₀ ≤ k' := by omega
        rcases this with _ | _
        · left; use k - k'; omega
        right; use k' - k; omega
      rcases h with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · convert le_of_lt (hw n l ?_ hl) with j hj; field_simp; grind; omega
      rw [← Complex.norm_conj, map_sum]
      convert le_of_lt (hw n l ?_ hl) with j hj
      simp [← Circle.coe_inv_eq_conj]; field_simp; grind; omega
    _ ≤ _ := by
      simp [sum_add_distrib]; gcongr 1
      · grind
      calc
        _ ≤ ∑ k ∈ range K, ((2 * k₀) * n ^ 2 : ℝ) := by
          apply sum_le_sum; intro k hk
          simp [← sum_filter]; gcongr; norm_cast
          convert card_le_card_of_injOn (t := range (2 * k₀)) (fun a ↦ a + k₀ - k) _ _
          · simp
          · intro a; grind
          intro a b _; grind
        _ = _ := by simp

/-- **Tao's solution to Question 1.** For any sequence $z : \mathbb{N} \to \mathrm{Circle}$,
$$\limsup_{k \to \infty} \limsup_{n \to \infty} \left\| \sum_{j < n} z_j^k \right\| = \infty.$$

The proof:
1. Assume for contradiction the iterated limsup equals some real $C$.
2. By `Circle.exists_shift_uniform_bound`, for any $K$ we get a shifted sequence $w$ with
   $\|\sum_{j < n} w_j^k\| < 2(C+1) =: C'$ uniformly in $n$, for $k \in [k_0, K]$.
3. By `Circle.l2_averaging_bound`, $n K^2 \le K^2 (C')^2 + K(2k_0 n^2)$.
4. Choosing $n > (C')^2 + 1$ and $K = 2 k_0 n^2 + 1$ violates this inequality.

Adapted from [teorth/analysis](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_987.lean). -/
@[category API, AMS 11]
theorem tao_circle (z : ℕ → Circle) :
    atTop.limsup (fun k : ℕ ↦ atTop.limsup (fun n : ℕ ↦
      (‖∑ j ∈ range n, ((z j) ^ k : ℂ)‖ : EReal))) = ⊤ := by
  generalize hC : atTop.limsup (fun k : ℕ ↦ atTop.limsup (fun n : ℕ ↦
    (‖∑ j ∈ range n, ((z j) ^ k : ℂ)‖ : EReal))) = C
  by_contra! h
  -- Step 1: Lift C to a real number.
  have hC_nonneg : 0 ≤ C := by
    subst hC
    apply_rules [le_limsup_of_frequently_le', Frequently.of_forall]; intro k
    apply_rules [le_limsup_of_frequently_le', Frequently.of_forall]; intro n
    positivity
  have hC_ne_bot : C ≠ ⊥ := by contrapose! hC_nonneg; simp_all
  lift C to ℝ using ⟨h, hC_ne_bot⟩
  -- Step 2: For each k ≥ k₀, partial sums are eventually < C+1.
  have hC' : (C : EReal) < (C + 1 : ℝ) := by norm_cast; linarith
  rw [← hC] at hC'; clear hC h hC_nonneg hC_ne_bot
  replace hC' := eventually_lt_of_limsup_lt hC'; rw [eventually_atTop] at hC'
  choose k₀ hk₀ using hC'
  replace hk₀ : ∀ k ≥ k₀, ∃ N, ∀ n ≥ N, ‖∑ j ∈ range n, ((z j) ^ k : ℂ)‖ < C + 1 := by
    peel hk₀ with k _ hk₀
    replace hk₀ := eventually_lt_of_limsup_lt hk₀; rw [eventually_atTop] at hk₀
    peel hk₀ with N _ n hn; norm_cast at hn
  -- Step 3: Pick n, K to derive contradiction.
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * (C + 1)) ^ 2 + 1)
  let K := 2 * k₀ * n ^ 2 + 1
  obtain ⟨w, hw⟩ := Circle.exists_shift_uniform_bound z C k₀ hk₀ K
  have key := Circle.l2_averaging_bound w k₀ K n hw
  have contra : (n : ℝ) * K ^ 2 > K ^ 2 * (2 * (C + 1)) ^ 2 + K * ((2 * k₀) * n ^ 2) := calc
    _ > ((2 * (C + 1)) ^ 2 + 1) * K ^ 2 := by gcongr
    _ = K ^ 2 * (2 * (C + 1)) ^ 2 + K * K := by ring
    _ ≥ _ := by gcongr; simp [K]
  linarith

/- ## Question 1, Question 2, and historical lower-bound variants -/

/-- Question 1:

Is it true that $\limsup_{k \to \infty} A_k = \infty$?

Erdős [Er64b] remarks it is "easy to see" that $\limsup_k \sup_n |\sum_{j \le n} e(k x_j)| = \infty$.
Erdős [Er65b] later found a "very easy" proof that $A_k \gg \log k$ for infinitely many $k$.
Clunie [Cl67] proved that $A_k \gg k^{1/2}$ for infinitely many $k$, which implies the answer is
yes (Tao independently found a proof). This is Problem 7.21 in [Ha74].

The proof here is the "second proof" given in the discussion at erdosproblems.com/987,
adapted from Tao's formalisation at
[teorth/analysis](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_987.lean).
-/
@[category research solved, AMS 11 40 42]
theorem erdos_987.parts.i :
    answer(True) ↔ ∀ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      atTop.limsup (fun k : ℕ => A x k) = ⊤ := by
  refine ⟨fun _ x _ => ?_, fun _ => trivial⟩
  -- Set z j = e (x j) ∈ Circle
  let z : ℕ → Circle := fun j => ⟨e (x j), mem_sphere_zero_iff_norm.mpr (norm_e (x j))⟩
  -- ((z j) ^ k : ℂ) = (e (x j)) ^ k = e (k * x j)
  have key : ∀ k j : ℕ, ((z j) ^ k : ℂ) = e ((k : ℝ) * x j) := by
    intro k j
    show (e (x j)) ^ k = e ((k : ℝ) * x j)
    exact e_pow_eq (x j) k
  -- Reduce to Tao's theorem on Circle
  have h := tao_circle z
  have eq_funcs : (fun k : ℕ => A x k) =
      (fun k : ℕ => atTop.limsup (fun n : ℕ =>
        (‖∑ j ∈ range n, ((z j) ^ k : ℂ)‖ : EReal))) := by
    funext k
    unfold A
    congr 1
    funext n
    congr 2
    exact Finset.sum_congr rfl fun j _ => (key k j).symm
  rw [eq_funcs]
  exact h

/- ## Question 2

Is it possible for $A_k = o(k)$?

The answer is yes — `parts.ii` is proved later in the file as a corollary of
`erdos_987.variants.sqrt_log_upper_bound`, which gives a $\sqrt{k \log k}$
bound, and the asymptotic $\sqrt{k \log k} = o(k)$. -/

/-- Erdős [Er64b] remarks it is "easy to see" that for every infinite sequence
$x_1, x_2, \ldots \in (0, 1)$,
$$\limsup_{k \to \infty} \sup_n \left\lvert \sum_{j \le n} e(k x_j) \right\rvert = \infty.$$

Direct corollary of `parts.i`: the inner $\sup_n$ is at least $\limsup_n$ pointwise in $k$, so
$\limsup_k \sup_n \ge \limsup_k \limsup_n = \infty$. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.sup_limsup_infty
    (x : ℕ → ℝ) (hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    atTop.limsup (fun k : ℕ =>
      ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) = ⊤ := by
  have h_parts := (erdos_987.parts.i).mp trivial x hx
  refine top_le_iff.mp ?_
  rw [← h_parts]
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun k => ?_)
  -- Show A x k ≤ ⨆ n, ‖partial sum n‖.
  show atTop.limsup (fun n : ℕ =>
    ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) ≤
    ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)
  exact Filter.limsup_le_iSup

/-- **Bound for $|e(t) - 1|$ via distance to integers.** $\|e(t) - 1\| \le 2\pi |t - \mathrm{round}(t)|$.

Proof: `‖e t - 1‖ = |2 sin(π t)|` by `Complex.norm_exp_I_mul_ofReal_sub_one`. Writing
$t = (t - \mathrm{round}(t)) + r$ for the integer $r = \mathrm{round}(t)$, $\sin(\pi t) =
\pm \sin(\pi (t - r))$ using `Real.sin_int_mul_pi`. Then `|sin(π s)| ≤ π|s|` via
`Real.abs_sin_le_abs`. -/
@[category API, AMS 11]
lemma e_sub_one_norm_le (t : ℝ) : ‖e t - 1‖ ≤ 2 * Real.pi * |t - round t| := by
  -- e t = exp(I · 2πt).
  have h1 : ‖e t - 1‖ = |2 * Real.sin (Real.pi * t)| := by
    rw [e]
    rw [show ((2 * Real.pi * t : ℝ) * Complex.I) = Complex.I * (2 * Real.pi * t : ℝ) from by ring]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    congr 1
    ring_nf
  rw [h1]
  -- |sin(π t)| = |sin(π (t - round t))| via π·integer addition.
  have hsin_eq : |Real.sin (Real.pi * t)| = |Real.sin (Real.pi * (t - round t))| := by
    rw [show Real.pi * t = Real.pi * (t - round t) + (round t : ℝ) * Real.pi from by ring]
    rw [Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  -- Bound |sin(π (t - round t))| ≤ π |t - round t|.
  calc |2 * Real.sin (Real.pi * t)| = 2 * |Real.sin (Real.pi * t)| := by rw [abs_mul, abs_of_pos]; norm_num
    _ = 2 * |Real.sin (Real.pi * (t - round t))| := by rw [hsin_eq]
    _ ≤ 2 * |Real.pi * (t - round t)| := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        exact Real.abs_sin_le_abs
    _ = 2 * Real.pi * |t - round t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]; ring

/-- **Bound for $|e(t) - 1|$ via $|t|$.** $\|e(t) - 1\| \le 2\pi |t|$.

Since $0$ is an integer, `round_le t 0` yields `|t - round t| ≤ |t - 0| = |t|`; combine with
`e_sub_one_norm_le`. -/
@[category API, AMS 11]
lemma e_sub_one_norm_le_abs (t : ℝ) : ‖e t - 1‖ ≤ 2 * Real.pi * |t| := by
  refine (e_sub_one_norm_le t).trans ?_
  have h_le : |t - round t| ≤ |t| := by
    have h := round_le t 0
    simpa using h
  exact mul_le_mul_of_nonneg_left h_le (by positivity)

/-- Erdős [Er65b] proved that, for every infinite sequence $x_1, x_2, \ldots \in (0, 1)$,
$A_k \gg \log k$ for infinitely many $k$.

**Proof outline (Erdős 1965).**

1. Use the quantitative simultaneous Dirichlet (`Real.exists_simul_dirichlet`) with $Q = 7$:
   for any $n$ reals $y_1, \ldots, y_n$, there exists $1 \le k \le 7^n$ with
   $|k y_i - \mathrm{round}(k y_i)| < 1/7$ for all $i$. This gives
   $\mathrm{Re}\,e(k y_i) > 1 - 2\pi/7 > 1/10$ (using $|2\sin(\pi t)| \le 2\pi |t|$).
2. **Offset trick.** Apply the lemma to $\{N x_{rn+i}\}_{i=1}^n$ for the block starting at
   $rn+1$. Get $k' \le 7^n$ with the property; set $k_r := k' \cdot N$. Then $N \le k_r
   \le N \cdot 7^n$ and $|k_r x_{rn+i} - \mathrm{round}(\cdot)| < 1/7$ for $i = 1, \ldots, n$.
3. **Pigeonhole on $r$.** Since $k_r \in \{N, \ldots, N\cdot 7^n\}$ (finite),
   `Finite.exists_infinite_fiber` gives $k^* \in [N, N \cdot 7^n]$ with $k_r = k^*$ for
   infinitely many $r$.
4. For each such $r$: $|S_{(r+1)n}(k^*) - S_{rn}(k^*)| > n / 20$, so by triangle inequality
   $\max(|S_{(r+1)n}(k^*)|, |S_{rn}(k^*)|) > n / 40$. Hence $A_{k^*} \ge n / 40$.
5. **Quantitative bound.** $\log k^* \le \log N + n \log 7$. With $c = 1/(40 \log 7)$ and
   $n \ge \log N / \log 7$, we get $n/40 \ge c (\log N + n \log 7) \ge c \log k^*$. Thus
   $A_{k^*} \ge c \log k^*$ with $k^* \ge N$, proving $\exists^\infty k$ in `atTop`. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.log_lower_bound
    (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c > 0, ∃ᶠ k : ℕ in atTop, ((c * Real.log k : ℝ) : EReal) ≤ A x k := by
  -- Constants: log 7 > 0, c = 1/(40·log 7), and the partial-sum constant
  -- (1 - 2π/7)/2 > 1/20.
  have hlog7_pos : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h2pi_lt_7_9_10 : 2 * Real.pi < 7 * (9 / 10 : ℝ) := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    linarith
  -- 1 - 2π/7 > 1/10.
  have h_one_sub_pos : (1 / 10 : ℝ) < 1 - 2 * Real.pi / 7 := by
    have h7 : (0 : ℝ) < 7 := by norm_num
    have hbd : 2 * Real.pi / 7 < 9 / 10 := by
      rw [div_lt_iff₀ h7]
      linarith
    linarith
  refine ⟨1 / (40 * Real.log 7), by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  -- Choose n so that n ≥ 1 and Real.log (N+1) ≤ n * Real.log 7.
  have hN1_pos : (0 : ℝ) < (N + 1 : ℕ) := by exact_mod_cast Nat.succ_pos N
  -- We need n ≥ Real.log (N+1) / Real.log 7. Use Archimedean.
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (Real.log (N + 1 : ℕ) / Real.log 7)
  set n := max 1 n₀ with hn_def
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
  have hn_ge_one : 1 ≤ n := hn_pos
  have hn_ge : (Real.log (N + 1 : ℕ) / Real.log 7) ≤ n := by
    refine hn₀.trans ?_
    exact_mod_cast le_max_right _ _
  have hn_log_bd : Real.log (N + 1 : ℕ) ≤ n * Real.log 7 := by
    rw [div_le_iff₀ hlog7_pos] at hn_ge
    exact hn_ge
  -- For each r, apply Real.exists_simul_dirichlet with the n reals
  -- y_r(i) = (N+1) * x (r*n + i)  and Q = 7.
  have h_dirichlet_each : ∀ r : ℕ, ∃ k' : ℕ, 0 < k' ∧ k' ≤ 7 ^ n ∧
      ∀ i : Fin n, |(k' : ℝ) * ((N + 1 : ℕ) * x (r * n + i)) -
        round ((k' : ℝ) * ((N + 1 : ℕ) * x (r * n + i)))| < 1 / 7 := by
    intro r
    exact Real.exists_simul_dirichlet (fun i : Fin n => (N + 1 : ℕ) * x (r * n + i))
      (by norm_num : (0 : ℕ) < 7)
  choose k' hk'_pos hk'_le hk'_dir using h_dirichlet_each
  -- For each r, set k(r) := k'(r) * (N+1). Then (N+1) ≤ k(r) ≤ (N+1) * 7^n.
  set kk : ℕ → ℕ := fun r => k' r * (N + 1) with hkk_def
  have hkk_lower : ∀ r, N + 1 ≤ kk r := fun r => by
    simp only [hkk_def]
    have := hk'_pos r
    calc N + 1 = 1 * (N + 1) := (one_mul _).symm
      _ ≤ k' r * (N + 1) := Nat.mul_le_mul_right _ this
  have hkk_upper : ∀ r, kk r ≤ (N + 1) * 7 ^ n := fun r => by
    simp only [hkk_def, Nat.mul_comm (k' r)]
    exact Nat.mul_le_mul_left (N + 1) (hk'_le r)
  -- The Dirichlet bound translates: |k(r) * x_{rn+i} - round(...)| < 1/7.
  have hkk_dir : ∀ r : ℕ, ∀ i : Fin n,
      |(kk r : ℝ) * x (r * n + i) - round ((kk r : ℝ) * x (r * n + i))| < 1 / 7 := by
    intro r i
    have h := hk'_dir r i
    have hrew : (kk r : ℝ) * x (r * n + i) =
        (k' r : ℝ) * ((N + 1 : ℕ) * x (r * n + i)) := by
      simp only [hkk_def]
      push_cast
      ring
    rw [hrew]
    exact h
  -- Pigeonhole: kk : ℕ → Fin ((N + 1) * 7 ^ n + 1) (clipped, but kk r is already in range).
  -- Use Finite.exists_infinite_fiber.
  let M := (N + 1) * 7 ^ n
  have hkk_in_range : ∀ r, kk r < M + 1 := fun r => by
    have := hkk_upper r
    show kk r < M + 1
    omega
  let f : ℕ → Fin (M + 1) := fun r => ⟨kk r, hkk_in_range r⟩
  obtain ⟨k_star_fin, hk_star_inf⟩ := Finite.exists_infinite_fiber f
  -- k_star = k_star_fin.val.
  set kStar := k_star_fin.val with hkStar_def
  -- The preimage f⁻¹ {k_star_fin} is infinite.
  have hk_star_lower : N + 1 ≤ kStar := by
    -- Pick any r in the preimage; kk r = kStar ≥ N + 1.
    obtain ⟨r, hr⟩ := hk_star_inf.nonempty
    have hkk_eq : kk r = kStar := by
      have : f r = k_star_fin := hr
      simpa [f, hkStar_def] using congrArg Fin.val this
    rw [← hkk_eq]
    exact hkk_lower r
  have hk_star_upper : kStar ≤ M := by
    have h := k_star_fin.isLt
    show kStar ≤ M
    omega
  -- We claim k_star ≥ N.
  have hk_star_ge_N : N ≤ kStar := by
    have := hk_star_lower
    omega
  -- Define R = {r : ℕ | kk r = kStar}. This is infinite.
  set R : Set ℕ := f ⁻¹' {k_star_fin} with hR_def
  have hR_inf : R.Infinite := by
    have : Infinite R := hk_star_inf
    exact Set.infinite_coe_iff.mp this
  -- For r ∈ R, |kStar * x_{rn+i} - round(...)| < 1/7 (since kk r = kStar).
  have hkStar_dir : ∀ r ∈ R, ∀ i : Fin n,
      |(kStar : ℝ) * x (r * n + i) - round ((kStar : ℝ) * x (r * n + i))| < 1 / 7 := by
    intro r hr i
    have hkk_eq : kk r = kStar := by
      have hf : f r = k_star_fin := hr
      simpa [f, hkStar_def] using congrArg Fin.val hf
    rw [← hkk_eq]
    exact hkk_dir r i
  -- For each r ∈ R, the sum ∑_{j ∈ [rn, (r+1)n)} e(kStar · x_j) has real part ≥ n(1 - 2π/7).
  -- (Each summand has Re ≥ 1 - 2π/7.)
  have hRe_each : ∀ r ∈ R, ∀ i : Fin n,
      (1 - 2 * Real.pi / 7 : ℝ) ≤ (e ((kStar : ℝ) * x (r * n + i))).re := by
    intro r hr i
    have hbd := hkStar_dir r hr i
    have hnorm := e_sub_one_norm_le ((kStar : ℝ) * x (r * n + i))
    -- ‖e t - 1‖ ≤ 2π · |...| < 2π / 7.
    have h1 : ‖e ((kStar : ℝ) * x (r * n + i)) - 1‖ < 2 * Real.pi / 7 := by
      have hπ : 0 < 2 * Real.pi := by positivity
      have h := mul_lt_mul_of_pos_left hbd hπ
      have heq : 2 * Real.pi * (1 / 7) = 2 * Real.pi / 7 := by ring
      rw [heq] at h
      exact lt_of_le_of_lt hnorm h
    -- 1 - Re(e(...)) ≤ ‖e(...) - 1‖.
    have h2 : 1 - (e ((kStar : ℝ) * x (r * n + i))).re ≤
        ‖e ((kStar : ℝ) * x (r * n + i)) - 1‖ := by
      have hre : (e ((kStar : ℝ) * x (r * n + i)) - 1).re =
          (e ((kStar : ℝ) * x (r * n + i))).re - 1 := by
        simp [Complex.sub_re]
      have hle : (e ((kStar : ℝ) * x (r * n + i)) - 1).re ≤
          ‖e ((kStar : ℝ) * x (r * n + i)) - 1‖ :=
        Complex.re_le_norm _
      have hle' : -((e ((kStar : ℝ) * x (r * n + i))).re - 1) ≤
          ‖e ((kStar : ℝ) * x (r * n + i)) - 1‖ := by
        have habs := Complex.abs_re_le_norm (e ((kStar : ℝ) * x (r * n + i)) - 1)
        rw [hre] at habs
        have := abs_le.mp habs
        linarith
      linarith
    linarith
  -- The constant for the partial-sum bound.
  set δ : ℝ := (1 - 2 * Real.pi / 7) / 2 with hδ_def
  have hδ_lb : (1 / 20 : ℝ) < δ := by
    simp only [hδ_def]
    linarith
  have hδ_pos : 0 < δ := by linarith
  -- Block sum: define `S m = ∑ j ∈ range m, e (kStar * x j)`. Then for r ∈ R,
  -- `(S ((r+1)*n) - S (r*n)).re ≥ n * (1 - 2π/7)`.
  set S : ℕ → ℂ := fun m => ∑ j ∈ range m, e ((kStar : ℝ) * x j) with hS_def
  have h_block_re : ∀ r ∈ R,
      (n : ℝ) * (1 - 2 * Real.pi / 7) ≤ (S ((r + 1) * n) - S (r * n)).re := by
    intro r hr
    -- S ((r+1)*n) - S (r*n) = ∑ j ∈ Ico (r*n) ((r+1)*n), e (kStar * x j)
    have h_diff : S ((r + 1) * n) - S (r * n) =
        ∑ j ∈ Finset.Ico (r * n) ((r + 1) * n), e ((kStar : ℝ) * x j) := by
      simp only [hS_def]
      rw [show range ((r + 1) * n) =
        range (r * n) ∪ Finset.Ico (r * n) ((r + 1) * n) from ?_]
      · rw [Finset.sum_union]
        · ring
        · refine Finset.disjoint_left.mpr fun a ha hb => ?_
          rw [Finset.mem_range] at ha
          rw [Finset.mem_Ico] at hb
          omega
      · ext a
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        constructor
        · intro h
          by_cases hr' : a < r * n
          · left; exact hr'
          · right; refine ⟨by omega, h⟩
        · intro h
          rcases h with h | h
          · have hrn : r * n ≤ (r + 1) * n := by
              rw [Nat.add_one_mul]; omega
            omega
          · exact h.2
    rw [h_diff]
    -- Re of the block sum = ∑ Re of summands ≥ n * (1 - 2π/7).
    rw [Complex.re_sum]
    -- Reindex: j ∈ Ico (r*n) ((r+1)*n) corresponds to j = r*n + i for i ∈ range n.
    have hreindex : ∑ j ∈ Finset.Ico (r * n) ((r + 1) * n),
          (e ((kStar : ℝ) * x j)).re =
        ∑ i ∈ range n, (e ((kStar : ℝ) * x (r * n + i))).re := by
      rw [show ((r + 1) * n) = r * n + n from by rw [Nat.add_one_mul]]
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show (r * n + n - r * n) = n from by omega]
    rw [hreindex]
    -- Each summand ≥ 1 - 2π/7. Sum is ≥ n * (1 - 2π/7).
    have hbound : ∀ i ∈ range n,
        (1 - 2 * Real.pi / 7 : ℝ) ≤ (e ((kStar : ℝ) * x (r * n + i))).re := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact hRe_each r hr ⟨i, hi⟩
    calc (n : ℝ) * (1 - 2 * Real.pi / 7)
        = ∑ _ ∈ range n, (1 - 2 * Real.pi / 7 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [mul_comm]
      _ ≤ ∑ i ∈ range n, (e ((kStar : ℝ) * x (r * n + i))).re :=
          Finset.sum_le_sum hbound
  -- From Re(S_{(r+1)n} - S_{rn}) ≥ n * (1 - 2π/7), we get
  -- |S_{(r+1)n} - S_{rn}| ≥ n * (1 - 2π/7), and so
  -- max(|S_{(r+1)n}|, |S_{rn}|) ≥ n * (1 - 2π/7) / 2 = n * δ.
  have h_block_norm : ∀ r ∈ R,
      (n : ℝ) * (1 - 2 * Real.pi / 7) ≤ ‖S ((r + 1) * n) - S (r * n)‖ := by
    intro r hr
    have hre := h_block_re r hr
    have h := Complex.re_le_norm (S ((r + 1) * n) - S (r * n))
    linarith
  have h_max_bound : ∀ r ∈ R,
      (n : ℝ) * δ ≤ max ‖S ((r + 1) * n)‖ ‖S (r * n)‖ := by
    intro r hr
    have hbn := h_block_norm r hr
    -- ‖S_{(r+1)n} - S_{rn}‖ ≤ ‖S_{(r+1)n}‖ + ‖S_{rn}‖ ≤ 2 * max(...)
    have htri := norm_sub_le (S ((r + 1) * n)) (S (r * n))
    have hmax_le : ‖S ((r + 1) * n)‖ + ‖S (r * n)‖ ≤
        2 * max ‖S ((r + 1) * n)‖ ‖S (r * n)‖ := by
      rcases le_total ‖S ((r + 1) * n)‖ ‖S (r * n)‖ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hcomb : (n : ℝ) * (1 - 2 * Real.pi / 7) ≤
        2 * max ‖S ((r + 1) * n)‖ ‖S (r * n)‖ := by
      linarith
    simp only [hδ_def]
    linarith
  -- Build the witness: there are infinitely many m's with ‖S m‖ ≥ n * δ.
  -- Specifically, for each r ∈ R, either (r+1)*n or r*n is such an m. Since n ≥ 1,
  -- (r+1)*n ≥ n ≥ 1, and as r → ∞ along R, both r*n and (r+1)*n → ∞.
  -- The set {(r+1)*n | r ∈ R} ∪ {r*n | r ∈ R} is infinite.
  -- Frequently along atTop: ‖S m‖ ≥ n * δ.
  have h_freq : ∃ᶠ m : ℕ in atTop, (n : ℝ) * δ ≤ ‖S m‖ := by
    rw [Filter.frequently_atTop]
    intro M
    -- Find r ∈ R with r * n ≥ M.
    -- Since n ≥ 1 and R is infinite, pick r ∈ R with r ≥ M. Then r * n ≥ M.
    obtain ⟨r, hr_in, hr_ge⟩ : ∃ r ∈ R, M ≤ r := by
      by_contra hcontra
      push_neg at hcontra
      have hsub : R ⊆ (Finset.range M : Set ℕ) := by
        intro r hr
        have := hcontra r hr
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      exact hR_inf ((Finset.range M).finite_toSet.subset hsub)
    have hrn_ge : M ≤ r * n := by
      calc M ≤ r := hr_ge
        _ = r * 1 := (mul_one _).symm
        _ ≤ r * n := Nat.mul_le_mul_left _ hn_ge_one
    have h_max := h_max_bound r hr_in
    -- max(‖S ((r+1)*n)‖, ‖S (r*n)‖) ≥ n * δ. Pick whichever is the larger.
    by_cases hcase : ‖S (r * n)‖ ≤ ‖S ((r + 1) * n)‖
    · refine ⟨(r + 1) * n, ?_, ?_⟩
      · calc M ≤ r * n := hrn_ge
          _ ≤ (r + 1) * n := Nat.mul_le_mul_right _ (Nat.le_succ _)
      · rw [max_eq_left hcase] at h_max
        exact h_max
    · push_neg at hcase
      refine ⟨r * n, hrn_ge, ?_⟩
      rw [max_eq_right hcase.le] at h_max
      exact h_max
  -- Conclude: A x kStar ≥ n * δ ≥ c * log kStar, with kStar ≥ N.
  refine ⟨kStar, hk_star_ge_N, ?_⟩
  -- A x kStar = limsup over m of ‖S m‖ ≥ n * δ.
  have h_A_lb : (((n : ℝ) * δ : ℝ) : EReal) ≤ A x kStar := by
    rw [A]
    refine le_limsup_of_frequently_le' ?_
    refine h_freq.mono fun m hm => ?_
    exact_mod_cast hm
  -- Now show c * log kStar ≤ n * δ.
  -- log kStar ≤ log ((N+1) * 7^n) = log (N+1) + n * log 7 ≤ 2 * n * log 7.
  have hkStar_pos : 0 < kStar := by omega
  have hkStar_real_pos : (0 : ℝ) < kStar := by exact_mod_cast hkStar_pos
  have h_log_kStar : Real.log kStar ≤ 2 * (n : ℝ) * Real.log 7 := by
    have hk_le_M : (kStar : ℝ) ≤ ((N + 1) * 7 ^ n : ℕ) := by
      exact_mod_cast hk_star_upper
    have h1 : Real.log kStar ≤ Real.log ((N + 1) * 7 ^ n : ℕ) := by
      refine Real.log_le_log hkStar_real_pos ?_
      exact_mod_cast hk_le_M
    have hN1pos : (0 : ℝ) < ((N + 1) * 7 ^ n : ℕ) := by
      positivity
    have hpush : (((N + 1) * 7 ^ n : ℕ) : ℝ) = (N + 1 : ℕ) * (7 : ℝ) ^ n := by
      push_cast; ring
    rw [hpush] at h1
    have hN1real_pos : (0 : ℝ) < (N + 1 : ℕ) := hN1_pos
    have h7_pos : (0 : ℝ) < (7 : ℝ) ^ n := by positivity
    have h2 : Real.log ((N + 1 : ℕ) * (7 : ℝ) ^ n) =
        Real.log (N + 1 : ℕ) + Real.log ((7 : ℝ) ^ n) := by
      exact Real.log_mul hN1real_pos.ne' h7_pos.ne'
    have h3 : Real.log ((7 : ℝ) ^ n) = n * Real.log 7 := by
      rw [Real.log_pow]
    rw [h2, h3] at h1
    linarith
  -- Now combine: c * log kStar ≤ c * (2 n log 7) ≤ n / 20 ≤ n * δ.
  have h_c_log : (1 / (40 * Real.log 7) : ℝ) * Real.log kStar ≤ (n : ℝ) * δ := by
    have h1 : (1 / (40 * Real.log 7) : ℝ) * Real.log kStar ≤
        (1 / (40 * Real.log 7) : ℝ) * (2 * (n : ℝ) * Real.log 7) := by
      have hcpos : 0 < (1 / (40 * Real.log 7) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left h_log_kStar hcpos.le
    have h2 : (1 / (40 * Real.log 7) : ℝ) * (2 * (n : ℝ) * Real.log 7) =
        (n : ℝ) / 20 := by
      have hlog7ne : Real.log 7 ≠ 0 := hlog7_pos.ne'
      field_simp
      ring
    have h3 : (n : ℝ) / 20 ≤ (n : ℝ) * δ := by
      have hnnn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have : (1 / 20 : ℝ) ≤ δ := hδ_lb.le
      calc (n : ℝ) / 20 = (n : ℝ) * (1 / 20) := by ring
        _ ≤ (n : ℝ) * δ := mul_le_mul_of_nonneg_left this hnnn
    linarith
  -- Cast and conclude.
  calc ((1 / (40 * Real.log 7) * Real.log kStar : ℝ) : EReal)
      ≤ (((n : ℝ) * δ : ℝ) : EReal) := by exact_mod_cast h_c_log
    _ ≤ A x kStar := h_A_lb

/- ## Clunie's `sqrt_lower_bound` proof: Lemma 1 (Parseval inequality)

The proof of `sqrt_lower_bound` factors through two analytic lemmas of Clunie [Cl67]:

- **Lemma 1** (this section): a Parseval-style lower bound on the power-sum series
  of points on the unit circle.
- **Lemma 2** (next section): a subset-selection lemma that, under the contradiction
  hypothesis $\limsup_v A_v/\sqrt{v} \le c$, picks $\zeta_1,\ldots,\zeta_n$ from
  $\{e(x_v)\}$ with controlled power-sums.

Both lemmas are fully proven below, and the final deduction is split into the helpers
`clunie_range_C_bound` and `clunie_exp_decay_contradiction`, with `sqrt_lower_bound`
combining everything.
-/

/-- Power sum of unit-circle points: $s_k(\zeta) = \zeta_1^k + \cdots + \zeta_n^k$. -/
noncomputable def clunieS {n : ℕ} (ζ : Fin n → ℂ) (k : ℕ) : ℂ := ∑ v, (ζ v) ^ k

/-- The constant term of the power sum: $s_0 = n$. -/
@[category API, AMS 11]
lemma clunieS_zero {n : ℕ} (ζ : Fin n → ℂ) : clunieS ζ 0 = n := by
  simp [clunieS]

/-- $|s_k| \le n$ when each $|\zeta_v| = 1$ (triangle inequality). -/
@[category API, AMS 11]
lemma norm_clunieS_le {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1) (k : ℕ) :
    ‖clunieS ζ k‖ ≤ n := by
  calc ‖clunieS ζ k‖ ≤ ∑ v, ‖(ζ v) ^ k‖ := norm_sum_le _ _
    _ = ∑ _ : Fin n, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [norm_pow, hζ v, one_pow]
    _ = n := by simp

/-- The function $\varphi(\theta) = \sum_{v=1}^n \frac{1}{1 - \zeta_v r e^{2\pi i \theta}}$
on the unit interval. This is the holomorphic function (in $z = re^{2\pi i \theta}$) whose
Parseval identity drives Clunie's Lemma 1. Its Taylor coefficients in $z$ are exactly the
power sums $s_0 = n, s_1, s_2, \ldots$. -/
noncomputable def cluniePhi {n : ℕ} (ζ : Fin n → ℂ) (r : ℝ) (θ : ℝ) : ℂ :=
  ∑ v, (1 - (ζ v) * (r : ℂ) * e θ)⁻¹

/-- The single summand of $\varphi$, $f_v(\theta) = 1/(1 - \zeta_v r e^{2\pi i \theta})$. -/
noncomputable def cluniePhiTerm (ζ : ℂ) (r : ℝ) (θ : ℝ) : ℂ :=
  (1 - ζ * (r : ℂ) * e θ)⁻¹

@[category API, AMS 11]
lemma cluniePhi_eq_sum {n : ℕ} (ζ : Fin n → ℂ) (r : ℝ) (θ : ℝ) :
    cluniePhi ζ r θ = ∑ v, cluniePhiTerm (ζ v) r θ := rfl

/-- The denominator $1 - \zeta r e(\theta)$ is nonzero when $\|\zeta\| = 1$ and
$0 \le r < 1$, since $\|\zeta r e(\theta)\| = r < 1$. -/
@[category API, AMS 11]
lemma one_sub_zeta_r_e_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) : (1 - ζ * (r : ℂ) * e θ) ≠ 0 := by
  intro h
  have h1 : ζ * (r : ℂ) * e θ = 1 := by linear_combination -h
  have h2 : ‖ζ * (r : ℂ) * e θ‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, norm_e, mul_one] at h2
  linarith

/-- $e(\theta) = \mathrm{circleMap}\, 0\, 1\, (2\pi\theta)$. -/
@[category API, AMS 11]
lemma e_eq_circleMap (θ : ℝ) :
    e θ = circleMap 0 1 (2 * Real.pi * θ) := by
  unfold e circleMap
  simp [Complex.ofReal_mul]

/-- **Cauchy's integral formula in the $e(\theta)$ parametrization.** If $g$ is continuous on
the closed unit disk and differentiable on the open unit disk, then
$\int_0^1 g(e(\theta))\,d\theta = g(0)$. This is Cauchy's formula at $w = 0$ rewritten in the
parametrization $z = e(\theta) = \exp(2\pi i\theta)$. -/
@[category API, AMS 11]
theorem integral_holomorphic_on_disk (g : ℂ → ℂ)
    (hg_cont : ContinuousOn g (Metric.closedBall (0 : ℂ) 1))
    (hg_diff : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ g z) :
    ∫ θ in (0 : ℝ)..1, g (e θ) = g 0 := by
  -- Apply Cauchy's integral formula at w = 0.
  have h_zero_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hCauchy : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∮ z in C((0 : ℂ), 1), (z - (0 : ℂ))⁻¹ • g z = g 0 :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) (Set.countable_empty) h_zero_in_ball hg_cont
      (fun x hx => hg_diff x hx.1)
  simp only [sub_zero] at hCauchy
  -- Unfold circleIntegral.
  have h_circle : (∮ z in C((0 : ℂ), 1), z⁻¹ • g z) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.I * g (circleMap 0 1 θ) := by
    rw [circleIntegral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [deriv_circleMap]
    have h_ne : circleMap 0 1 θ ≠ 0 := by
      intro h_eq
      have := (circleMap_mem_sphere (0 : ℂ) (zero_le_one) θ)
      rw [h_eq, mem_sphere_iff_norm, sub_zero, norm_zero] at this
      exact zero_ne_one this
    rw [smul_eq_mul, smul_eq_mul]
    field_simp
  rw [h_circle] at hCauchy
  rw [intervalIntegral.integral_const_mul] at hCauchy
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 := by
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi_ne, Complex.I_ne_zero]
  have h_two_pi_C : (∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 1 θ)) =
      ((2 * Real.pi : ℝ) : ℂ) * g 0 := by
    have h := hCauchy
    rw [smul_eq_mul] at h
    have h1 : Complex.I * (∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 1 θ)) =
        2 * (Real.pi : ℂ) * Complex.I * g 0 := by
      have step : (2 * (Real.pi : ℂ) * Complex.I) *
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.I * (∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 1 θ)))) =
          (2 * (Real.pi : ℂ) * Complex.I) * g 0 := by
        rw [h]
      rw [← mul_assoc, mul_inv_cancel₀ h2πI_ne, one_mul] at step
      exact step
    have h2 : (∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 1 θ)) =
        2 * (Real.pi : ℂ) * g 0 := by
      have step := h1.trans (by ring : (2 * (Real.pi : ℂ) * Complex.I * g 0 =
        Complex.I * (2 * (Real.pi : ℂ) * g 0)))
      exact mul_left_cancel₀ Complex.I_ne_zero step
    rw [h2]
    push_cast
    ring
  -- Substitute θ = 2π · u.
  have h2π_ne : (2 * Real.pi : ℝ) ≠ 0 := by
    have := Real.pi_ne_zero
    positivity
  have hsub := intervalIntegral.integral_comp_mul_left
    (a := 0) (b := 1) (c := 2 * Real.pi)
    (f := fun θ => g (circleMap 0 1 θ)) h2π_ne
  rw [mul_zero, mul_one] at hsub
  -- Identify circleMap 0 1 (2π θ) = e θ.
  have h_e_eq : (fun θ => g (e θ)) = fun θ => g (circleMap 0 1 (2 * Real.pi * θ)) := by
    funext θ; rw [e_eq_circleMap]
  rw [h_e_eq, hsub, h_two_pi_C]
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- **Lemma A.** For $\alpha \in \mathbb{C}$ with $\|\alpha\| < 1$,
$\int_0^1 (1 - \alpha e(\theta))^{-1}\,d\theta = 1$.

Direct application of `integral_holomorphic_on_disk` to $f(z) = (1 - \alpha z)^{-1}$ (which
is holomorphic on $\|z\| < 1/\|\alpha\|$, containing the closed unit disk). -/
@[category API, AMS 11]
theorem integral_inv_one_sub_alpha_e {α : ℂ} (hα : ‖α‖ < 1) :
    ∫ θ in (0 : ℝ)..1, (1 - α * e θ)⁻¹ = 1 := by
  have h_one_sub_ne : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (1 - α * z) ≠ 0 := by
    intro z hz h
    have hαz_eq : α * z = 1 := by linear_combination -h
    have hαz_norm : ‖α * z‖ = 1 := by rw [hαz_eq, norm_one]
    rw [norm_mul] at hαz_norm
    have hz_le_one : ‖z‖ ≤ 1 := by simpa using hz
    nlinarith [norm_nonneg α, norm_nonneg z]
  have hf_cont : ContinuousOn (fun z : ℂ => (1 - α * z)⁻¹) (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    apply ContinuousAt.inv₀
    · exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
    · exact h_one_sub_ne z hz
  have hf_diff : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (fun z : ℂ => (1 - α * z)⁻¹) z := by
    intro z hz
    apply DifferentiableAt.inv
    · exact (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)
    · exact h_one_sub_ne z (Metric.ball_subset_closedBall hz)
  have := integral_holomorphic_on_disk _ hf_cont hf_diff
  simpa using this

/-- $e(a + b) = e(a) \cdot e(b)$. -/
@[category API, AMS 11]
lemma e_add (a b : ℝ) : e (a + b) = e a * e b := by
  unfold e
  rw [show ((2 * Real.pi * (a + b) : ℝ) * Complex.I) =
      ((2 * Real.pi * a : ℝ) * Complex.I) + ((2 * Real.pi * b : ℝ) * Complex.I) from by
    push_cast; ring]
  exact Complex.exp_add _ _

/-- $e(-\theta) = (e(\theta))^{-1}$. -/
@[category API, AMS 11]
lemma e_neg (θ : ℝ) : e (-θ) = (e θ)⁻¹ := by
  have h_prod : e θ * e (-θ) = 1 := by
    rw [← e_add]
    rw [show (θ + -θ : ℝ) = 0 from by ring]
    exact e_zero
  exact eq_inv_of_mul_eq_one_right h_prod

/-- **Lemma B.** For $\alpha \in \mathbb{C}$ with $\|\alpha\| < 1$,
$$ \int_0^1 \frac{1}{e(\theta) - \alpha}\,d\theta = 0. $$

*Proof.* Use the algebraic identity
$$ \frac{1}{e(\theta) - \alpha} = \frac{e(-\theta)}{1 - \alpha e(-\theta)}, $$
then substitute $u = 1 - \theta$ (using $e(1 - \theta) = e(-\theta)$ since $e(1) = 1$):
$$ \int_0^1 \frac{e(-\theta)}{1 - \alpha e(-\theta)}\,d\theta
   = \int_0^1 \frac{e(u)}{1 - \alpha e(u)}\,du. $$
Algebraic manipulation: $e(u)/(1 - \alpha e(u)) = (1/\alpha)[1/(1 - \alpha e(u)) - 1]$ (when
$\alpha \ne 0$). Apply `integral_inv_one_sub_alpha_e` (Lemma A) and $\int_0^1 1\,du = 1$ to
get $(1/\alpha)(1 - 1) = 0$. The case $\alpha = 0$ reduces to $\int_0^1 e(-\theta)\,d\theta = 0$
by `integral_e_int_mul` with $m = -1$. -/
@[category API, AMS 11]
theorem integral_inv_e_sub_alpha {α : ℂ} (hα : ‖α‖ < 1) :
    ∫ θ in (0 : ℝ)..1, (e θ - α)⁻¹ = 0 := by
  -- Pointwise: (e θ - α)⁻¹ = e(-θ) · (1 - α · e(-θ))⁻¹.
  have h_e_norm : ∀ θ : ℝ, ‖e θ‖ = 1 := norm_e
  have h_eθ_ne : ∀ θ : ℝ, e θ ≠ α := by
    intro θ h
    have : ‖e θ‖ = ‖α‖ := by rw [h]
    rw [h_e_norm θ] at this
    linarith
  have h_one_sub_ne : ∀ θ : ℝ, (1 - α * e (-θ)) ≠ 0 := by
    intro θ h
    have hαe : α * e (-θ) = 1 := by linear_combination -h
    have hαe_norm : ‖α * e (-θ)‖ = 1 := by rw [hαe, norm_one]
    rw [norm_mul, h_e_norm (-θ), mul_one] at hαe_norm
    linarith
  have h_pt : ∀ θ : ℝ, (e θ - α)⁻¹ = e (-θ) * (1 - α * e (-θ))⁻¹ := by
    intro θ
    have heθ : e θ ≠ 0 := e_ne_zero θ
    have h_eθ_α : e θ - α ≠ 0 := sub_ne_zero.mpr (h_eθ_ne θ)
    have h_one_sub : 1 - α * e (-θ) ≠ 0 := h_one_sub_ne θ
    rw [e_neg θ]
    -- Goal: (e θ - α)⁻¹ = (e θ)⁻¹ * (1 - α * (e θ)⁻¹)⁻¹
    -- Rewrite: 1 - α * (e θ)⁻¹ = (e θ - α) * (e θ)⁻¹
    have hkey : (1 - α * (e θ)⁻¹) = (e θ - α) * (e θ)⁻¹ := by field_simp
    rw [hkey, mul_inv, inv_inv]
    rw [show (e θ)⁻¹ * ((e θ - α)⁻¹ * e θ) = (e θ - α)⁻¹ * ((e θ)⁻¹ * e θ) by ring,
        inv_mul_cancel₀ heθ, mul_one]
  rw [intervalIntegral.integral_congr (fun θ _ => h_pt θ)]
  -- Substitute θ ↦ 1 - θ using e(1-θ) = e(-θ) (since e(1) = 1).
  have h_e_one_sub : ∀ θ : ℝ, e (1 - θ) = e (-θ) := by
    intro θ
    rw [show (1 - θ : ℝ) = 1 + (-θ) from by ring, e_add]
    show e 1 * e (-θ) = e (-θ)
    rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) from by norm_cast]
    rw [e_intCast 1, one_mul]
  have h_subst_eq : (fun θ => e (-θ) * (1 - α * e (-θ))⁻¹) =
      (fun θ => e (1 - θ) * (1 - α * e (1 - θ))⁻¹) := by
    funext θ; rw [h_e_one_sub]
  rw [h_subst_eq]
  rw [intervalIntegral.integral_comp_sub_left (f := fun u => e u * (1 - α * e u)⁻¹) 1]
  simp only [sub_zero, sub_self]
  -- Goal: ∫_0^1 e u * (1 - α * e u)⁻¹ du = 0
  by_cases hα_zero : α = 0
  · subst hα_zero
    simp only [zero_mul, sub_zero, inv_one, mul_one]
    -- ∫ e θ dθ = 0 by integral_e_int_mul m = 1
    have := integral_e_int_mul 1
    rw [if_neg one_ne_zero] at this
    simpa using this
  · -- e u / (1 - α e u) = (1/α) (1/(1 - α e u) - 1)
    have h2_general : ∀ u : ℝ, (1 - α * e u) ≠ 0 := by
      intro u h
      have hαe : α * e u = 1 := by linear_combination -h
      have : ‖α * e u‖ = 1 := by rw [hαe, norm_one]
      rw [norm_mul, h_e_norm u, mul_one] at this
      linarith
    have h_id : ∀ u : ℝ, e u * (1 - α * e u)⁻¹ =
        α⁻¹ * ((1 - α * e u)⁻¹ - 1) := by
      intro u
      have h2 := h2_general u
      have hα_ne : α ≠ 0 := hα_zero
      rw [mul_comm α⁻¹ _, eq_mul_inv_iff_mul_eq₀ hα_ne]
      have hinv : (1 - α * e u) * (1 - α * e u)⁻¹ = 1 := mul_inv_cancel₀ h2
      linear_combination -hinv
    rw [intervalIntegral.integral_congr (fun u _ => h_id u)]
    rw [intervalIntegral.integral_const_mul]
    have h_int_split : ∫ u in (0 : ℝ)..1, ((1 - α * e u)⁻¹ - 1) =
        (∫ u in (0 : ℝ)..1, (1 - α * e u)⁻¹) - ∫ u in (0 : ℝ)..1, (1 : ℂ) := by
      apply intervalIntegral.integral_sub
      · -- (1 - α * e u)⁻¹ is integrable on [0, 1].
        apply ContinuousOn.intervalIntegrable
        apply Continuous.continuousOn
        rw [continuous_iff_continuousAt]
        intro θ
        apply ContinuousAt.inv₀
        · exact (continuous_const.sub (continuous_const.mul continuous_e)).continuousAt
        · exact h2_general θ
      · exact intervalIntegrable_const
    rw [h_int_split]
    rw [integral_inv_one_sub_alpha_e hα]
    simp

/-- $\int_0^1 e(\theta)/(1 - \alpha e(\theta))\,d\theta = 0$ for $\|\alpha\| < 1$.

*Proof.* For $\alpha = 0$ the integrand is $e(\theta)$, integral $0$ by `integral_e_int_mul`
with $m = 1$. For $\alpha \ne 0$, use the algebraic identity
$e(\theta)/(1 - \alpha e(\theta)) = (1/\alpha)((1 - \alpha e(\theta))^{-1} - 1)$ (linear
combination of $(1 - \alpha e(\theta)) \cdot (1 - \alpha e(\theta))^{-1} = 1$). Integrating
gives $(1/\alpha)(1 - 1) = 0$ via Lemma A. -/
@[category API, AMS 11]
theorem integral_e_div_one_sub_alpha_e {α : ℂ} (hα : ‖α‖ < 1) :
    ∫ θ in (0 : ℝ)..1, e θ * (1 - α * e θ)⁻¹ = 0 := by
  by_cases hα_zero : α = 0
  · subst hα_zero
    simp only [zero_mul, sub_zero, inv_one, mul_one]
    have := integral_e_int_mul 1
    rw [if_neg one_ne_zero] at this
    simpa using this
  · have h2_general : ∀ u : ℝ, (1 - α * e u) ≠ 0 := by
      intro u h
      have hαe : α * e u = 1 := by linear_combination -h
      have : ‖α * e u‖ = 1 := by rw [hαe, norm_one]
      rw [norm_mul, norm_e, mul_one] at this
      linarith
    have h_id : ∀ u : ℝ, e u * (1 - α * e u)⁻¹ =
        α⁻¹ * ((1 - α * e u)⁻¹ - 1) := by
      intro u
      have h2 := h2_general u
      have hα_ne : α ≠ 0 := hα_zero
      rw [mul_comm α⁻¹ _, eq_mul_inv_iff_mul_eq₀ hα_ne]
      have hinv : (1 - α * e u) * (1 - α * e u)⁻¹ = 1 := mul_inv_cancel₀ h2
      linear_combination -hinv
    rw [intervalIntegral.integral_congr (fun u _ => h_id u)]
    rw [intervalIntegral.integral_const_mul]
    have h_int_split : ∫ u in (0 : ℝ)..1, ((1 - α * e u)⁻¹ - 1) =
        (∫ u in (0 : ℝ)..1, (1 - α * e u)⁻¹) - ∫ u in (0 : ℝ)..1, (1 : ℂ) := by
      apply intervalIntegral.integral_sub
      · apply ContinuousOn.intervalIntegrable
        apply Continuous.continuousOn
        rw [continuous_iff_continuousAt]
        intro θ
        apply ContinuousAt.inv₀
        · exact (continuous_const.sub (continuous_const.mul continuous_e)).continuousAt
        · exact h2_general θ
      · exact intervalIntegrable_const
    rw [h_int_split, integral_inv_one_sub_alpha_e hα]
    simp

/-- $\int_0^1 e(\theta)/(e(\theta) - \beta)\,d\theta = 1$ for $\|\beta\| < 1$.

*Proof.* $e(\theta)/(e(\theta) - \beta) = 1 + \beta/(e(\theta) - \beta)$. The first piece
integrates to $1$, the second to $\beta \cdot 0 = 0$ by Lemma B. -/
@[category API, AMS 11]
theorem integral_e_div_e_sub_beta {β : ℂ} (hβ : ‖β‖ < 1) :
    ∫ θ in (0 : ℝ)..1, e θ * (e θ - β)⁻¹ = 1 := by
  have h_eθβ : ∀ θ : ℝ, e θ - β ≠ 0 := by
    intro θ h
    have heq : e θ = β := by linear_combination h
    have : ‖e θ‖ = ‖β‖ := by rw [heq]
    rw [norm_e] at this
    linarith
  have h_id : ∀ θ : ℝ, e θ * (e θ - β)⁻¹ = 1 + β * (e θ - β)⁻¹ := by
    intro θ
    have h := h_eθβ θ
    have hinv : (e θ - β) * (e θ - β)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination hinv
  rw [intervalIntegral.integral_congr (fun θ _ => h_id θ)]
  have h_int_inv : Continuous fun θ : ℝ => (e θ - β)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro θ
    apply ContinuousAt.inv₀
    · exact (continuous_e.sub continuous_const).continuousAt
    · exact h_eθβ θ
  have h_int_const_mul : IntervalIntegrable (fun θ : ℝ => β * (e θ - β)⁻¹) MeasureTheory.volume
      0 1 := (continuous_const.mul h_int_inv).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const) h_int_const_mul,
    intervalIntegral.integral_const_mul, integral_inv_e_sub_alpha hβ]
  simp

/-- **Same-direction product integral.** For $\alpha, \beta \in \mathbb{C}$ with
$\|\alpha\|, \|\beta\| < 1$,
$$\int_0^1 (1 - \alpha e(\theta))^{-1} (1 - \beta e(\theta))^{-1}\,d\theta = 1.$$

Direct application of `integral_holomorphic_on_disk` to the holomorphic function
$g(z) = 1/((1-\alpha z)(1-\beta z))$, with $g(0) = 1$. -/
@[category API, AMS 11]
theorem integral_inv_one_sub_α_e_mul_inv_one_sub_β_e {α β : ℂ}
    (hα : ‖α‖ < 1) (hβ : ‖β‖ < 1) :
    ∫ θ in (0 : ℝ)..1, (1 - α * e θ)⁻¹ * (1 - β * e θ)⁻¹ = 1 := by
  have h_one_sub : ∀ (γ : ℂ), ‖γ‖ < 1 → ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      (1 - γ * z) ≠ 0 := by
    intro γ hγ z hz h
    have hγz_eq : γ * z = 1 := by linear_combination -h
    have : ‖γ * z‖ = 1 := by rw [hγz_eq, norm_one]
    rw [norm_mul] at this
    have hz_le : ‖z‖ ≤ 1 := by simpa using hz
    nlinarith [norm_nonneg γ, norm_nonneg z]
  have hg_cont : ContinuousOn (fun z : ℂ => (1 - α * z)⁻¹ * (1 - β * z)⁻¹)
      (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    apply ContinuousAt.mul
    · exact ContinuousAt.inv₀
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (h_one_sub α hα z hz)
    · exact ContinuousAt.inv₀
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
        (h_one_sub β hβ z hz)
  have hg_diff : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (fun z : ℂ => (1 - α * z)⁻¹ * (1 - β * z)⁻¹) z := by
    intro z hz
    refine DifferentiableAt.mul ?_ ?_ <;> apply DifferentiableAt.inv
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul differentiableAt_id)
    · exact h_one_sub α hα z (Metric.ball_subset_closedBall hz)
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul differentiableAt_id)
    · exact h_one_sub β hβ z (Metric.ball_subset_closedBall hz)
  have := integral_holomorphic_on_disk _ hg_cont hg_diff
  simpa using this

/-- **Opposite-direction product integral.** For $\alpha, \beta' \in \mathbb{C}$ with
$\|\alpha\|, \|\beta'\| < 1$,
$$ \int_0^1 (1 - \alpha e(\theta))^{-1} \cdot \frac{e(\theta)}{e(\theta) - \beta'}\,d\theta
   = \frac{1}{1 - \alpha \beta'}. $$

*Proof.* Partial fractions: $1/((1-\alpha z)(z-\beta')) = (\alpha/(1-\alpha\beta'))/(1-\alpha z)
+ (1/(1-\alpha\beta'))/(z-\beta')$. Apply `integral_e_div_one_sub_alpha_e` (= 0) and
`integral_e_div_e_sub_beta` (= 1) to each piece. -/
@[category API, AMS 11]
theorem integral_inv_one_sub_α_e_mul_e_div_e_sub_β {α β' : ℂ}
    (hα : ‖α‖ < 1) (hβ' : ‖β'‖ < 1) :
    ∫ θ in (0 : ℝ)..1, (1 - α * e θ)⁻¹ * (e θ * (e θ - β')⁻¹) = (1 - α * β')⁻¹ := by
  have hαβ_ne : (1 - α * β') ≠ 0 := by
    intro h
    have : α * β' = 1 := by linear_combination -h
    have hnorm : ‖α * β'‖ = 1 := by rw [this, norm_one]
    rw [norm_mul] at hnorm
    nlinarith [norm_nonneg α, norm_nonneg β']
  have h2 : ∀ θ : ℝ, (1 - α * e θ) ≠ 0 := by
    intro θ h
    have hαe : α * e θ = 1 := by linear_combination -h
    have hnorm : ‖α * e θ‖ = 1 := by rw [hαe, norm_one]
    rw [norm_mul, norm_e, mul_one] at hnorm
    linarith
  have h3 : ∀ θ : ℝ, (e θ - β') ≠ 0 := by
    intro θ h
    have heq : e θ = β' := by linear_combination h
    have : ‖e θ‖ = ‖β'‖ := by rw [heq]
    rw [norm_e] at this
    linarith
  have h_pf : ∀ θ : ℝ, (1 - α * e θ)⁻¹ * (e θ * (e θ - β')⁻¹) =
      (α * (1 - α * β')⁻¹) * (e θ * (1 - α * e θ)⁻¹) +
      ((1 - α * β')⁻¹) * (e θ * (e θ - β')⁻¹) := by
    intro θ
    have h2θ := h2 θ
    have h3θ := h3 θ
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => h_pf θ)]
  have h_int1 : Continuous fun θ : ℝ => e θ * (1 - α * e θ)⁻¹ := by
    apply Continuous.mul continuous_e
    rw [continuous_iff_continuousAt]
    intro θ
    apply ContinuousAt.inv₀
    · exact (continuous_const.sub (continuous_const.mul continuous_e)).continuousAt
    · exact h2 θ
  have h_int2 : Continuous fun θ : ℝ => e θ * (e θ - β')⁻¹ := by
    apply Continuous.mul continuous_e
    rw [continuous_iff_continuousAt]
    intro θ
    apply ContinuousAt.inv₀
    · exact (continuous_e.sub continuous_const).continuousAt
    · exact h3 θ
  rw [intervalIntegral.integral_add
    ((continuous_const.mul h_int1).intervalIntegrable _ _)
    ((continuous_const.mul h_int2).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_e_div_one_sub_alpha_e hα, integral_e_div_e_sub_beta hβ']
  ring

/-- $\overline{e(\theta)} = e(-\theta) = (e(\theta))^{-1}$. -/
@[category API, AMS 11]
lemma conj_e (θ : ℝ) : (starRingEnd ℂ) (e θ) = (e θ)⁻¹ := by
  have h_norm : ‖e θ‖ = 1 := norm_e θ
  have h_norm_sq : Complex.normSq (e θ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h_norm]; norm_num
  have h_ne : e θ ≠ 0 := e_ne_zero θ
  have h_mul : e θ * (starRingEnd ℂ) (e θ) = 1 := by
    rw [Complex.mul_conj, h_norm_sq]; rfl
  exact eq_inv_of_mul_eq_one_right h_mul

/-- **Conjugate of `cluniePhiTerm`**: $\overline{f_\zeta(\theta)} = e(\theta) /
(e(\theta) - \bar\zeta\,r)$. -/
@[category API, AMS 11]
lemma conj_cluniePhiTerm (ζ : ℂ) (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : ℝ) : (starRingEnd ℂ) (cluniePhiTerm ζ r θ) =
      e θ * (e θ - (starRingEnd ℂ) ζ * (r : ℂ))⁻¹ := by
  unfold cluniePhiTerm
  have h_e_ne : e θ ≠ 0 := e_ne_zero θ
  have h_one_sub_ne : (1 - ζ * (r : ℂ) * e θ) ≠ 0 := one_sub_zeta_r_e_ne_zero hζ hr0 hr1 θ
  have h_eβ_ne : e θ - (starRingEnd ℂ) ζ * (r : ℂ) ≠ 0 := by
    intro h
    have heq : e θ = (starRingEnd ℂ) ζ * (r : ℂ) := by linear_combination h
    have : ‖e θ‖ = ‖(starRingEnd ℂ) ζ * (r : ℂ)‖ := by rw [heq]
    rw [norm_e, norm_mul, Complex.norm_conj, hζ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, one_mul] at this
    linarith
  rw [map_inv₀]
  rw [show (starRingEnd ℂ) (1 - ζ * (r : ℂ) * e θ) =
      1 - (starRingEnd ℂ) ζ * (r : ℂ) * (e θ)⁻¹ by
    simp [Complex.conj_ofReal, conj_e]]
  -- Goal: (1 - conj(ζ) r (e θ)⁻¹)⁻¹ = e θ * (e θ - conj(ζ) r)⁻¹
  -- Both sides multiplied by (e θ - conj(ζ) r):
  -- LHS · (e θ - conj(ζ) r) = (1 - conj(ζ) r/e θ)⁻¹ · (e θ - conj(ζ) r)
  --                         = e θ · (e θ - conj(ζ) r)⁻¹ · (e θ - conj(ζ) r)·(e θ)⁻¹·... too tangled
  -- Cleaner: 1 - conj(ζ) r/e θ = (e θ - conj(ζ) r)/e θ.
  have h_rewrite : (1 - (starRingEnd ℂ) ζ * (r : ℂ) * (e θ)⁻¹) =
      (e θ - (starRingEnd ℂ) ζ * (r : ℂ)) * (e θ)⁻¹ := by
    field_simp
  rw [h_rewrite, mul_inv, inv_inv]
  ring

/-- Continuity of `cluniePhiTerm ζ r` in $\theta$. -/
@[category API, AMS 11]
lemma continuous_cluniePhiTerm {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (cluniePhiTerm ζ r) := by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.inv₀
  · exact (continuous_const.sub
      ((continuous_const.mul continuous_const).mul continuous_e)).continuousAt
  · exact one_sub_zeta_r_e_ne_zero hζ hr0 hr1 θ

/-- Continuity of `cluniePhi ζ r` in $\theta$. -/
@[category API, AMS 11]
lemma continuous_cluniePhi {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : Continuous (cluniePhi ζ r) := by
  rw [show cluniePhi ζ r = fun θ => ∑ v, cluniePhiTerm (ζ v) r θ from rfl]
  exact continuous_finset_sum _ (fun v _ => continuous_cluniePhiTerm (hζ v) hr0 hr1)

/-- **Per-pair integral identity** (heart of Clunie's Lemma 1 lower bound). For
$\zeta_u, \zeta_v$ on the unit circle and $0 \le r < 1$,
$$ \int_0^1 \mathrm{Re}\bigl(\tfrac{1}{1-\zeta_u r e(\theta)}\bigr) \cdot
   \mathrm{Re}\bigl(\tfrac{1}{1-\zeta_v r e(\theta)}\bigr)\, d\theta
   \;=\; \tfrac{1}{2} + \tfrac{1}{2} \mathrm{Re}\bigl(\tfrac{1}{1-\zeta_u \bar\zeta_v r^2}\bigr). $$

*Proof outline.* Write $\mathrm{Re}\,w = (w + \bar w)/2$. The product
$(\mathrm{Re}\,f_u)(\mathrm{Re}\,f_v) = \tfrac{1}{4}(f_u + \bar f_u)(f_v + \bar f_v)$
expands into four cross terms, each of which is $1/((1-\alpha e(\theta))(1-\beta e(\sigma\theta)))$
for some $\alpha, \beta$ on the disk and $\sigma \in \{\pm 1\}$. Partial fractions in $e(\theta)$
together with `integral_inv_one_sub_alpha_e` (Lemma A) and `integral_inv_e_sub_alpha`
(Lemma B) compute each:
- Same direction ($\sigma = +1$, both factors): $\int f_u f_v\, d\theta = 1$ (from two
  Lemma A applications via partial fractions).
- Opposite direction: $\int f_u \bar f_v\, d\theta = 1/(1 - \zeta_u \bar\zeta_v r^2)$ (Lemma A
  + Lemma B via partial fractions on $e(\theta)$).
- $\int \bar f_u f_v$ is the conjugate.
- $\int \bar f_u \bar f_v$ is again $1$ (by symmetry).
Combining: $(1 + 1/(1-\zeta_u\bar\zeta_v r^2) + \overline{1/(1-\zeta_u\bar\zeta_v r^2)} + 1)/4
= 1/2 + (1/2)\mathrm{Re}(1/(1-\zeta_u\bar\zeta_v r^2))$. -/
@[category API, AMS 11 40 42]
theorem cluniePhi_per_pair_integral {ζu ζv : ℂ} (hζu : ‖ζu‖ = 1) (hζv : ‖ζv‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..1, (cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re =
      1 / 2 + (1 / 2) * (1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2)⁻¹.re := by
  -- Notation.
  set αu : ℂ := ζu * (r : ℂ) with hαu_def
  set αv : ℂ := ζv * (r : ℂ) with hαv_def
  set βu : ℂ := (starRingEnd ℂ) ζu * (r : ℂ) with hβu_def
  set βv : ℂ := (starRingEnd ℂ) ζv * (r : ℂ) with hβv_def
  -- Norm bounds.
  have hr_nn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hαu_lt : ‖αu‖ < 1 := by rw [hαu_def, norm_mul, hζu, hr_nn, one_mul]; exact hr1
  have hαv_lt : ‖αv‖ < 1 := by rw [hαv_def, norm_mul, hζv, hr_nn, one_mul]; exact hr1
  have hβu_lt : ‖βu‖ < 1 := by
    rw [hβu_def, norm_mul, Complex.norm_conj, hζu, hr_nn, one_mul]; exact hr1
  have hβv_lt : ‖βv‖ < 1 := by
    rw [hβv_def, norm_mul, Complex.norm_conj, hζv, hr_nn, one_mul]; exact hr1
  -- f_u f_v = 1 (same-direction).
  have hT1 : ∫ θ in (0:ℝ)..1, cluniePhiTerm ζu r θ * cluniePhiTerm ζv r θ = 1 := by
    show ∫ θ in (0:ℝ)..1, (1 - αu * e θ)⁻¹ * (1 - αv * e θ)⁻¹ = 1
    exact integral_inv_one_sub_α_e_mul_inv_one_sub_β_e hαu_lt hαv_lt
  -- f_u · conj(f_v) = (1 - αu βv)⁻¹ (opposite-direction).
  have hT2 : ∫ θ in (0:ℝ)..1, cluniePhiTerm ζu r θ * (starRingEnd ℂ) (cluniePhiTerm ζv r θ) =
      (1 - αu * βv)⁻¹ := by
    rw [intervalIntegral.integral_congr (fun θ _ => by rw [conj_cluniePhiTerm ζv hζv hr0 hr1])]
    show ∫ θ in (0:ℝ)..1, (1 - αu * e θ)⁻¹ * (e θ * (e θ - βv)⁻¹) = (1 - αu * βv)⁻¹
    exact integral_inv_one_sub_α_e_mul_e_div_e_sub_β hαu_lt hβv_lt
  -- conj(f_u) · f_v = (1 - αv βu)⁻¹ (opposite-direction, swapped).
  have hT3 : ∫ θ in (0:ℝ)..1, (starRingEnd ℂ) (cluniePhiTerm ζu r θ) * cluniePhiTerm ζv r θ =
      (1 - αv * βu)⁻¹ := by
    rw [intervalIntegral.integral_congr (fun θ _ => by
      rw [conj_cluniePhiTerm ζu hζu hr0 hr1, mul_comm])]
    show ∫ θ in (0:ℝ)..1, (1 - αv * e θ)⁻¹ * (e θ * (e θ - βu)⁻¹) = (1 - αv * βu)⁻¹
    exact integral_inv_one_sub_α_e_mul_e_div_e_sub_β hαv_lt hβu_lt
  -- conj(f_u) · conj(f_v) = 1 (same direction after substitution θ ↦ 1-θ).
  have hT4 : ∫ θ in (0:ℝ)..1,
      (starRingEnd ℂ) (cluniePhiTerm ζu r θ) * (starRingEnd ℂ) (cluniePhiTerm ζv r θ) = 1 := by
    rw [intervalIntegral.integral_congr (fun θ _ => by
      rw [conj_cluniePhiTerm ζu hζu hr0 hr1, conj_cluniePhiTerm ζv hζv hr0 hr1])]
    -- ∫ (e θ (e θ - βu)⁻¹) (e θ (e θ - βv)⁻¹) dθ
    -- We rewrite using e(-θ) = (e θ)⁻¹: (e θ (e θ - βu)⁻¹) = (1 - βu e(-θ))⁻¹.
    -- Then substitute θ ↦ 1-θ (e(1-θ) = e(-θ) since e(1) = 1).
    have h_eθ_β : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ θ : ℝ,
        e θ * (e θ - (starRingEnd ℂ) ζ * (r : ℂ))⁻¹ =
        (1 - (starRingEnd ℂ) ζ * (r : ℂ) * e (-θ))⁻¹ := by
      intro ζ hζ θ
      have hβ_lt : ‖(starRingEnd ℂ) ζ * (r : ℂ)‖ < 1 := by
        rw [norm_mul, Complex.norm_conj, hζ, hr_nn, one_mul]; exact hr1
      have h_e_ne : e θ ≠ 0 := e_ne_zero θ
      have h_one_sub : 1 - (starRingEnd ℂ) ζ * (r : ℂ) * e (-θ) ≠ 0 := by
        intro h
        have : (starRingEnd ℂ) ζ * (r : ℂ) * e (-θ) = 1 := by linear_combination -h
        have hnorm : ‖(starRingEnd ℂ) ζ * (r : ℂ) * e (-θ)‖ = 1 := by rw [this, norm_one]
        rw [norm_mul, norm_e, mul_one, norm_mul, Complex.norm_conj, hζ, hr_nn, one_mul] at hnorm
        linarith
      rw [e_neg]
      field_simp
    rw [intervalIntegral.integral_congr
      (fun θ _ => by rw [h_eθ_β ζu hζu, h_eθ_β ζv hζv])]
    -- Now substitute u = 1 - θ.
    have h_e_one_sub : ∀ θ : ℝ, e (-θ) = e (1 - θ) := by
      intro θ
      rw [show (1 - θ : ℝ) = 1 + (-θ) from by ring, e_add]
      rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) from by norm_cast]
      rw [e_intCast, one_mul]
    rw [intervalIntegral.integral_congr
      (fun θ _ => by rw [h_e_one_sub])]
    rw [intervalIntegral.integral_comp_sub_left
      (f := fun u => (1 - βu * e u)⁻¹ * (1 - βv * e u)⁻¹) 1]
    simp only [sub_zero, sub_self]
    exact integral_inv_one_sub_α_e_mul_inv_one_sub_β_e hβu_lt hβv_lt
  -- Pointwise: 4·(Re f_u)(Re f_v) (cast to ℂ) = (f_u + conj f_u)(f_v + conj f_v).
  have h_pt : ∀ θ : ℝ,
      (((cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re : ℝ) : ℂ) =
      (1 / 4) * (
        cluniePhiTerm ζu r θ * cluniePhiTerm ζv r θ +
        cluniePhiTerm ζu r θ * (starRingEnd ℂ) (cluniePhiTerm ζv r θ) +
        (starRingEnd ℂ) (cluniePhiTerm ζu r θ) * cluniePhiTerm ζv r θ +
        (starRingEnd ℂ) (cluniePhiTerm ζu r θ) * (starRingEnd ℂ) (cluniePhiTerm ζv r θ)
      ) := by
    intro θ
    push_cast
    rw [Complex.re_eq_add_conj (cluniePhiTerm ζu r θ),
      Complex.re_eq_add_conj (cluniePhiTerm ζv r θ)]
    ring
  -- Integrate the cast version over [0, 1].
  have h_int_complex : ((∫ θ in (0:ℝ)..1,
        (cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re : ℝ) : ℂ) =
      (1 / 4) * (1 + (1 - αu * βv)⁻¹ + (1 - αv * βu)⁻¹ + 1) := by
    rw [show (((∫ θ in (0:ℝ)..1,
          (cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re : ℝ) : ℂ)) =
        ∫ θ in (0:ℝ)..1, (((cluniePhiTerm ζu r θ).re *
          (cluniePhiTerm ζv r θ).re : ℝ) : ℂ) from
      (intervalIntegral.integral_ofReal).symm]
    rw [intervalIntegral.integral_congr (fun θ _ => h_pt θ)]
    -- Pull out the (1/4) constant and split the four integrals.
    rw [intervalIntegral.integral_const_mul]
    congr 1
    -- Need to integrate the sum of 4 functions; use integral_add iteratively.
    have hI1 : Continuous fun θ : ℝ =>
        cluniePhiTerm ζu r θ * cluniePhiTerm ζv r θ :=
      (continuous_cluniePhiTerm hζu hr0 hr1).mul (continuous_cluniePhiTerm hζv hr0 hr1)
    have hI2 : Continuous fun θ : ℝ =>
        cluniePhiTerm ζu r θ * (starRingEnd ℂ) (cluniePhiTerm ζv r θ) :=
      (continuous_cluniePhiTerm hζu hr0 hr1).mul
        (Complex.continuous_conj.comp (continuous_cluniePhiTerm hζv hr0 hr1))
    have hI3 : Continuous fun θ : ℝ =>
        (starRingEnd ℂ) (cluniePhiTerm ζu r θ) * cluniePhiTerm ζv r θ :=
      (Complex.continuous_conj.comp (continuous_cluniePhiTerm hζu hr0 hr1)).mul
        (continuous_cluniePhiTerm hζv hr0 hr1)
    have hI4 : Continuous fun θ : ℝ =>
        (starRingEnd ℂ) (cluniePhiTerm ζu r θ) * (starRingEnd ℂ) (cluniePhiTerm ζv r θ) :=
      (Complex.continuous_conj.comp (continuous_cluniePhiTerm hζu hr0 hr1)).mul
        (Complex.continuous_conj.comp (continuous_cluniePhiTerm hζv hr0 hr1))
    rw [intervalIntegral.integral_add (((hI1.add hI2).add hI3).intervalIntegrable _ _)
      (hI4.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_add ((hI1.add hI2).intervalIntegrable _ _)
      (hI3.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_add (hI1.intervalIntegrable _ _)
      (hI2.intervalIntegrable _ _)]
    rw [hT1, hT2, hT3, hT4]
  -- (1 - αv βu) = conj(1 - αu βv) since αv βu = conj(αu βv).
  have h_conj_K : (1 - αv * βu : ℂ) = (starRingEnd ℂ) (1 - αu * βv) := by
    show (1 - ζv * (r : ℂ) * ((starRingEnd ℂ) ζu * (r : ℂ))) =
        (starRingEnd ℂ) (1 - ζu * (r : ℂ) * ((starRingEnd ℂ) ζv * (r : ℂ)))
    simp [Complex.conj_ofReal]
    ring
  -- Also identify (1 - αu βv) = (1 - ζu · conj(ζv) · r²).
  have h_K_eq : (1 - αu * βv : ℂ) = 1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2 := by
    show (1 - ζu * (r : ℂ) * ((starRingEnd ℂ) ζv * (r : ℂ))) =
        1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2
    ring
  -- The integral, cast to ℂ, equals 1/2 + (1/2) · K + (1/2) · conj K, divided by 2.
  -- Wait: (1 + K + conj K + 1)/4 = (2 + K + conj K)/4 = 1/2 + (K + conj K)/4
  --     = 1/2 + (2 Re K)/4 = 1/2 + (1/2) Re K.
  -- Take real part of h_int_complex.
  have h_re : (((∫ θ in (0:ℝ)..1,
        (cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re : ℝ) : ℂ).re) =
      (((1 : ℝ) / 2 + (1 / 2) * (1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2)⁻¹.re : ℝ) : ℂ).re := by
    rw [h_int_complex]
    -- (1/4)(1 + (1-αu·βv)⁻¹ + (1-αv·βu)⁻¹ + 1)
    -- = (1/4)(2 + K + conj K) where K = (1-αu·βv)⁻¹
    rw [show (1 - αv * βu : ℂ)⁻¹ = (starRingEnd ℂ) ((1 - αu * βv)⁻¹) by
      rw [h_conj_K, ← map_inv₀]]
    rw [h_K_eq]
    -- Goal: ((1/4) · (1 + K⁻¹ + conj K⁻¹ + 1)).re = (1/2 + (1/2) · K⁻¹.re : ℝ) cast to ℂ then .re
    set K : ℂ := (1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2)⁻¹ with hK_def
    have h_simp : ((1 : ℂ) / 4 * (1 + K + (starRingEnd ℂ) K + 1)).re =
        1 / 2 + 1 / 2 * K.re := by
      have h_one_quarter : ((1 : ℂ) / 4).re = 1 / 4 := by
        rw [show ((1 : ℂ) / 4) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.ofReal_re _
      have h_one_quarter_im : ((1 : ℂ) / 4).im = 0 := by
        rw [show ((1 : ℂ) / 4) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.ofReal_im _
      rw [Complex.mul_re, h_one_quarter, h_one_quarter_im]
      simp only [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [h_simp]
    rw [show ((1 : ℝ) / 2 + 1 / 2 * K.re : ℝ) = (1 / 2 + 1 / 2 * K.re) from rfl]
    rw [Complex.ofReal_re]
  -- The cast (real → complex → real) is identity.
  have h_real : ((((∫ θ in (0:ℝ)..1,
        (cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re : ℝ) : ℂ).re : ℝ)) =
      ∫ θ in (0:ℝ)..1, (cluniePhiTerm ζu r θ).re * (cluniePhiTerm ζv r θ).re :=
    Complex.ofReal_re _
  have h_real2 : ((((1 : ℝ) / 2 + (1 / 2) *
        (1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2)⁻¹.re : ℝ) : ℂ).re : ℝ) =
      1 / 2 + (1 / 2) * (1 - ζu * (starRingEnd ℂ) ζv * (r : ℂ) ^ 2)⁻¹.re :=
    Complex.ofReal_re _
  linarith [h_re, h_real, h_real2]

/-- **Positivity of $\mathrm{Re}(1/(1-w))$ for $\|w\| < 1$.** -/
@[category API, AMS 11]
lemma re_one_sub_inv_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ ((1 - w)⁻¹).re := by
  rw [Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  -- (1 - w).re = 1 - w.re ≥ 1 - |w| > 0 when |w| < 1.
  have h1 : (1 - w).re = 1 - w.re := by simp
  rw [h1]
  have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have h3 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) h2
  linarith

/-- The denominator's norm is bounded below by $1 - r > 0$. -/
@[category API, AMS 11]
lemma norm_one_sub_zeta_r_e_lower {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r < 1)
    (θ : ℝ) : 1 - r ≤ ‖1 - ζ * (r : ℂ) * e θ‖ := by
  -- ‖1 - w‖ ≥ |‖1‖ - ‖w‖| = |1 - r| = 1 - r since r ≤ 1.
  have hw : ‖ζ * (r : ℂ) * e θ‖ = r := by
    rw [norm_mul, norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, norm_e, mul_one]
  have h := norm_sub_norm_le (1 : ℂ) (ζ * (r : ℂ) * e θ)
  rw [norm_one, hw] at h
  linarith

/-- **Pairwise expansion of $\int|\varphi|^2$.** For any unit-modulus $\zeta_1,\ldots,\zeta_n$
and $0 \le r < 1$,
$$ \int_0^1 |\varphi(\theta)|^2\, d\theta = \sum_{u,v} \frac{1}{1 - \zeta_u \bar\zeta_v r^2}. $$

*Proof.* $\|w\|^2 = w \cdot \bar w$, so
$\|\varphi\|^2 = (\sum_u f_u)(\sum_v \bar f_v) = \sum_{u,v} f_u \bar f_v$. Apply
`integral_inv_one_sub_α_e_mul_e_div_e_sub_β` (after `conj_cluniePhiTerm`) to each pair. -/
@[category API, AMS 11]
theorem cluniePhi_normSq_integral_pairs {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((∫ θ in (0 : ℝ)..1, ‖cluniePhi ζ r θ‖ ^ 2 : ℝ) : ℂ) =
      ∑ u : Fin n, ∑ v : Fin n, (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹ := by
  have hr_nn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h_α (i : Fin n) : ‖ζ i * (r : ℂ)‖ < 1 := by
    rw [norm_mul, hζ i, hr_nn, one_mul]; exact hr1
  have h_β (i : Fin n) : ‖(starRingEnd ℂ) (ζ i) * (r : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_conj, hζ i, hr_nn, one_mul]; exact hr1
  -- Pointwise identity: ‖φ(θ)‖² (as ℂ) = Σ_{u,v} f_u(θ) · conj(f_v(θ)).
  have h_pt : ∀ θ : ℝ, ((‖cluniePhi ζ r θ‖ ^ 2 : ℝ) : ℂ) =
      ∑ u : Fin n, ∑ v : Fin n,
        cluniePhiTerm (ζ u) r θ * (starRingEnd ℂ) (cluniePhiTerm (ζ v) r θ) := by
    intro θ
    rw [show (‖cluniePhi ζ r θ‖ ^ 2 : ℝ) = (Complex.normSq (cluniePhi ζ r θ) : ℝ) by
      rw [Complex.normSq_eq_norm_sq]]
    rw [show ((Complex.normSq (cluniePhi ζ r θ) : ℝ) : ℂ) =
        cluniePhi ζ r θ * (starRingEnd ℂ) (cluniePhi ζ r θ) from
      Complex.mul_conj _ |>.symm]
    rw [cluniePhi_eq_sum, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  -- Integrate.
  rw [show ((∫ θ in (0 : ℝ)..1, ‖cluniePhi ζ r θ‖ ^ 2 : ℝ) : ℂ) =
      ∫ θ in (0 : ℝ)..1, ((‖cluniePhi ζ r θ‖ ^ 2 : ℝ) : ℂ) from
    intervalIntegral.integral_ofReal.symm]
  rw [intervalIntegral.integral_congr (fun θ _ => h_pt θ)]
  -- Swap finite sums and integral.
  have h_cont : ∀ u v : Fin n, Continuous fun θ : ℝ =>
      cluniePhiTerm (ζ u) r θ * (starRingEnd ℂ) (cluniePhiTerm (ζ v) r θ) := fun u v =>
    (continuous_cluniePhiTerm (hζ u) hr0 hr1).mul
      (Complex.continuous_conj.comp (continuous_cluniePhiTerm (hζ v) hr0 hr1))
  rw [intervalIntegral.integral_finset_sum
    (fun u _ => Continuous.intervalIntegrable
      (continuous_finset_sum _ fun v _ => h_cont u v) _ _)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [intervalIntegral.integral_finset_sum
    (fun v _ => (h_cont u v).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl fun v _ => ?_
  -- Apply opposite-direction integral.
  rw [intervalIntegral.integral_congr
    (fun θ _ => by rw [conj_cluniePhiTerm (ζ v) (hζ v) hr0 hr1])]
  rw [show cluniePhiTerm (ζ u) r = fun θ : ℝ => (1 - ζ u * (r : ℂ) * e θ)⁻¹ from rfl]
  have := integral_inv_one_sub_α_e_mul_e_div_e_sub_β (h_α u) (h_β v)
  rw [show ζ u * (r : ℂ) * ((starRingEnd ℂ) (ζ v) * (r : ℂ)) =
      ζ u * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2 by ring] at this
  exact this

/-- **Pairwise sum equals power-series sum.** Algebraic identity converting the finite
pairwise sum from `cluniePhi_normSq_integral_pairs` to the power-series form needed for
Lemma 1.

For each pair $(u, v)$, expand
$(1 - \zeta_u \bar\zeta_v r^2)^{-1} = \sum_{k=0}^\infty (\zeta_u \bar\zeta_v r^2)^k$
(geometric series; convergent since $\|\zeta_u \bar\zeta_v r^2\| = r^2 < 1$). Swap finite
sum and tsum (justified by absolute convergence). Then
$$ \sum_{u,v} (\zeta_u \bar\zeta_v r^2)^k = r^{2k} \cdot s_k \cdot \overline{s_k}
   = |s_k|^2 \cdot r^{2k} $$
where $s_k = \sum_v \zeta_v^k = \mathrm{clunieS}\,\zeta\,k$. Splitting off the $k = 0$ term
(which is $|s_0|^2 = n^2$) gives the claim. -/
@[category API, AMS 11]
theorem clunie_pairwise_to_power_series {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ u : Fin n, ∑ v : Fin n, (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹) =
    (((n : ℝ) ^ 2 + ∑' k : ℕ, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) : ℝ) : ℂ) := by
  have hr_nn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h_norm_lt : ∀ u v : Fin n, ‖(ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2‖ < 1 := by
    intro u v
    rw [norm_mul, norm_mul, hζ u, Complex.norm_conj, hζ v, norm_pow, hr_nn]
    nlinarith
  have h_summable : ∀ u v : Fin n,
      Summable (fun k : ℕ => ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k) :=
    fun u v => summable_geometric_of_norm_lt_one (h_norm_lt u v)
  -- Each pair: (1 - ...)⁻¹ = ∑' k, (...)^k.
  have h_geom : ∀ u v : Fin n,
      (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹ =
      ∑' k : ℕ, ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k :=
    fun u v => (tsum_geometric_of_norm_lt_one (h_norm_lt u v)).symm
  simp_rw [h_geom]
  -- Swap inner ∑ v with ∑' k: per fixed u.
  have h_swap_v : ∀ u : Fin n,
      ∑ v : Fin n, ∑' k : ℕ, ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k =
      ∑' k : ℕ, ∑ v : Fin n, ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k := by
    intro u
    exact (Summable.tsum_finsetSum (fun v _ => h_summable u v)).symm
  rw [Finset.sum_congr rfl (fun u _ => h_swap_v u)]
  -- Swap outer ∑ u with ∑' k.
  have h_summable_inner : ∀ u : Fin n,
      Summable (fun k : ℕ => ∑ v : Fin n,
        ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k) := by
    intro u
    exact summable_sum (fun v _ => h_summable u v)
  rw [(Summable.tsum_finsetSum (fun u _ => h_summable_inner u) : _).symm]
  -- Now ∑' k, ∑ u, ∑ v, (...)^k.
  -- Identify ∑_{u,v} (ζu·conj(ζv)·r²)^k = (∑_u ζu^k)(∑_v conj(ζv)^k)·r^{2k} = |s_k|²·r^{2k}.
  have h_inner_eq : ∀ k : ℕ,
      ∑ u : Fin n, ∑ v : Fin n, ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k =
      (clunieS ζ k * (starRingEnd ℂ) (clunieS ζ k)) * (r : ℂ) ^ (2 * k) := by
    intro k
    have h1 : ∀ u v : Fin n,
        ((ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2) ^ k =
        ((ζ u) ^ k) * ((starRingEnd ℂ) (ζ v)) ^ k * ((r : ℂ) ^ 2) ^ k := by
      intro u v; ring
    simp_rw [h1]
    rw [show ∀ k, ((r : ℂ) ^ 2) ^ k = (r : ℂ) ^ (2 * k) from fun k => by ring]
    rw [show (fun u : Fin n => ∑ v : Fin n, (ζ u) ^ k * ((starRingEnd ℂ) (ζ v)) ^ k * (r : ℂ) ^ (2 * k))
        = (fun u : Fin n => (ζ u) ^ k * (∑ v : Fin n, ((starRingEnd ℂ) (ζ v)) ^ k) * (r : ℂ) ^ (2 * k)) by
      funext u
      rw [← Finset.sum_mul, ← Finset.mul_sum]]
    rw [show (fun u : Fin n => (ζ u) ^ k * (∑ v, ((starRingEnd ℂ) (ζ v)) ^ k) * (r : ℂ) ^ (2 * k))
        = (fun u : Fin n => (ζ u) ^ k * ((∑ v, ((starRingEnd ℂ) (ζ v)) ^ k) * (r : ℂ) ^ (2 * k))) by
      funext u; ring]
    rw [← Finset.sum_mul]
    -- Now: (∑_u ζu^k) * ((∑_v conj(ζv)^k) * r^(2k)) = clunieS ζ k * (∑_v conj(ζv)^k) * r^(2k)
    show (clunieS ζ k) * ((∑ v : Fin n, ((starRingEnd ℂ) (ζ v)) ^ k) * (r : ℂ) ^ (2 * k)) =
        clunieS ζ k * (starRingEnd ℂ) (clunieS ζ k) * (r : ℂ) ^ (2 * k)
    have h_conj_sum : (∑ v : Fin n, ((starRingEnd ℂ) (ζ v)) ^ k) =
        (starRingEnd ℂ) (clunieS ζ k) := by
      unfold clunieS
      rw [map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_pow]
    rw [h_conj_sum]; ring
  simp_rw [h_inner_eq]
  -- Now: ∑' k, |s_k|² · r^{2k} = n² + ∑'_{k≥1} ...
  -- Identify s · conj(s) = ‖s‖²
  have h_norm_sq : ∀ k : ℕ,
      clunieS ζ k * (starRingEnd ℂ) (clunieS ζ k) = ((‖clunieS ζ k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h_norm_sq]
  -- Goal: ∑' k, ((‖s_k‖² : ℝ) : ℂ) · (r : ℂ)^(2k) = ((n² + ∑'_{k:ℕ} ‖s_{k+1}‖²·r^{2(k+1)} : ℝ) : ℂ)
  -- Split off k = 0 from LHS.
  have h_summable_norm : Summable
      (fun k : ℕ => ((‖clunieS ζ k‖ ^ 2 : ℝ) : ℂ) * (r : ℂ) ^ (2 * k)) := by
    have h_bound_summable : Summable (fun k : ℕ => (n : ℝ) ^ 2 * r ^ (2 * k)) := by
      apply Summable.mul_left
      have hr2 : ‖(r ^ 2 : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
        nlinarith
      have := summable_geometric_of_norm_lt_one hr2
      have heq : ∀ k : ℕ, r ^ (2 * k) = (r ^ 2) ^ k := fun k => by ring
      simpa [heq] using this
    apply h_bound_summable.of_norm_bounded
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [norm_pow, hr_nn]
    have hsk_le : ‖clunieS ζ k‖ ≤ n := norm_clunieS_le ζ hζ k
    have hsq_le : ‖clunieS ζ k‖ ^ 2 ≤ (n : ℝ) ^ 2 := by
      apply sq_le_sq' _ hsk_le
      linarith [norm_nonneg (clunieS ζ k)]
    have hr_pow_nn : (0 : ℝ) ≤ r ^ (2 * k) := pow_nonneg hr0 _
    nlinarith
  rw [h_summable_norm.tsum_eq_zero_add]
  simp only [mul_zero, pow_zero, mul_one, clunieS_zero]
  -- Goal: ‖(n : ℂ)‖² + ∑' k:ℕ, ‖s_{k+1}‖² · r^{2(k+1)} = ((n² + ...:ℝ):ℂ)
  push_cast
  rw [Complex.norm_natCast]
  push_cast
  ring

/-- **Clunie's Lemma 1, Parseval form** [Cl67]. The squared $L^2$ norm of $\varphi$ on
$[0, 1]$ equals the sum of squared moduli of the Taylor coefficients weighted by $r^{2k}$.

Combines `cluniePhi_normSq_integral_pairs` (pairwise expansion) with
`clunie_pairwise_to_power_series` (algebraic identity) and the trivial cast
between $\mathbb{R}$ and $\mathbb{C}$. -/
@[category API, AMS 11 40 42]
theorem cluniePhi_normSq_integral {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..1, ‖cluniePhi ζ r θ‖ ^ 2 =
      (n : ℝ) ^ 2 + ∑' k : ℕ, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) := by
  have h_pairs := cluniePhi_normSq_integral_pairs ζ hζ r hr0 hr1
  have h_alg := clunie_pairwise_to_power_series ζ hζ r hr0 hr1
  have h_combined : ((∫ θ in (0 : ℝ)..1, ‖cluniePhi ζ r θ‖ ^ 2 : ℝ) : ℂ) =
      (((n : ℝ) ^ 2 + ∑' k : ℕ, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) : ℝ) : ℂ) := by
    rw [h_pairs, h_alg]
  exact_mod_cast h_combined

/-- Pointwise: $(\mathrm{Re}\,z)^2 \le \|z\|^2$. -/
@[category API, AMS 11]
lemma sq_re_le_normSq (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
  rw [h]
  nlinarith [sq_nonneg z.im]

/-- Step 1 of `cluniePhi_normSq_integral_lower`: $\int \|\varphi\|^2 \ge \int (\mathrm{Re}\,
\varphi)^2$. -/
@[category API, AMS 11]
lemma cluniePhi_re_sq_integral_le_normSq {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..1, (cluniePhi ζ r θ).re ^ 2 ≤
      ∫ θ in (0 : ℝ)..1, ‖cluniePhi ζ r θ‖ ^ 2 := by
  have hphi_cont := continuous_cluniePhi ζ hζ hr0 hr1
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  · exact ((Complex.continuous_re.comp hphi_cont).pow 2).intervalIntegrable _ _
  · exact ((continuous_norm.comp hphi_cont).pow 2).intervalIntegrable _ _
  · intro θ _
    exact sq_re_le_normSq (cluniePhi ζ r θ)

/-- $\mathrm{Re}\,\varphi(\theta) = \sum_v \mathrm{Re}(f_v(\theta))$ for the summands
$f_v$. -/
@[category API, AMS 11]
lemma cluniePhi_re_eq_sum {n : ℕ} (ζ : Fin n → ℂ) (r : ℝ) (θ : ℝ) :
    (cluniePhi ζ r θ).re = ∑ v, (cluniePhiTerm (ζ v) r θ).re := by
  rw [cluniePhi_eq_sum]
  exact Complex.re_sum _ _

/-- Step 2 expansion: $\int (\mathrm{Re}\,\varphi)^2 \, d\theta
= \sum_{u,v} \int (\mathrm{Re}\, f_u)(\mathrm{Re}\, f_v) \, d\theta$. -/
@[category API, AMS 11]
lemma cluniePhi_re_sq_integral_eq_sum {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..1, (cluniePhi ζ r θ).re ^ 2 =
      ∑ u, ∑ v, ∫ θ in (0 : ℝ)..1,
        (cluniePhiTerm (ζ u) r θ).re * (cluniePhiTerm (ζ v) r θ).re := by
  -- Pointwise: (Re φ)² = Σ_{u,v} (Re f_u)(Re f_v).
  have h_pt : ∀ θ, (cluniePhi ζ r θ).re ^ 2 =
      ∑ u, ∑ v, (cluniePhiTerm (ζ u) r θ).re * (cluniePhiTerm (ζ v) r θ).re := by
    intro θ
    rw [cluniePhi_re_eq_sum, sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [intervalIntegral.integral_congr (fun θ _ => h_pt θ)]
  -- Swap finite sums and integrals.
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [intervalIntegral.integral_finset_sum]
    intro v _
    exact ((Complex.continuous_re.comp (continuous_cluniePhiTerm (hζ u) hr0 hr1)).mul
      (Complex.continuous_re.comp (continuous_cluniePhiTerm (hζ v) hr0 hr1))).intervalIntegrable
      _ _
  intro u _
  apply ContinuousOn.intervalIntegrable
  refine Continuous.continuousOn ?_
  exact continuous_finset_sum _ fun v _ =>
    (Complex.continuous_re.comp (continuous_cluniePhiTerm (hζ u) hr0 hr1)).mul
      (Complex.continuous_re.comp (continuous_cluniePhiTerm (hζ v) hr0 hr1))

/-- **Clunie's Lemma 1, lower-bound form** [Cl67]. Lower bound on the $L^2$ norm of
$\varphi$ via the positivity of $\mathrm{Re}\,\varphi$ in the disk:
$$ \int_0^1 |\varphi|^2 \, d\theta \;\ge\; \tfrac{n^2}{2} + \tfrac{n}{2(1-r^2)}. $$

*Proof.* $\int \|\varphi\|^2 \ge \int (\mathrm{Re}\,\varphi)^2$ pointwise. Expanding
$(\mathrm{Re}\,\varphi)^2 = (\sum_v b_v)^2 = \sum_{u,v} b_u b_v$ with
$b_v = \mathrm{Re}(1/(1-\zeta_v r e(\theta)))$ and applying `cluniePhi_per_pair_integral` term
by term gives $\sum_{u,v} (\tfrac{1}{2} + \tfrac{1}{2}\mathrm{Re}(\tfrac{1}{1-\zeta_u
\bar\zeta_v r^2}))$. Diagonal pairs ($u = v$) contribute exactly $\tfrac{1}{2} +
\tfrac{1}{2(1-r^2)}$ (since $|\zeta_u|^2 = 1$); off-diagonal pairs contribute at least
$\tfrac{1}{2}$ each by `re_one_sub_inv_nonneg`. Summing gives the claim. -/
@[category API, AMS 11 40 42]
theorem cluniePhi_normSq_integral_lower {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((n : ℝ) ^ 2 / 2 + (n : ℝ) / (2 * (1 - r ^ 2))) ≤
      ∫ θ in (0 : ℝ)..1, ‖cluniePhi ζ r θ‖ ^ 2 := by
  refine le_trans ?_ (cluniePhi_re_sq_integral_le_normSq ζ hζ hr0 hr1)
  rw [cluniePhi_re_sq_integral_eq_sum ζ hζ hr0 hr1]
  -- Apply per-pair identity term-by-term.
  have h_pair : ∀ u v : Fin n,
      ∫ θ in (0 : ℝ)..1, (cluniePhiTerm (ζ u) r θ).re * (cluniePhiTerm (ζ v) r θ).re =
        1 / 2 + (1 / 2) * (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹.re :=
    fun u v => cluniePhi_per_pair_integral (hζ u) (hζ v) hr0 hr1
  simp_rw [h_pair]
  -- Diagonal contribution: Re(1/(1 - 1·r²)) = 1/(1-r²).
  have h_diag_eq : ∀ u : Fin n, (1 - (ζ u) * (starRingEnd ℂ) (ζ u) * (r : ℂ) ^ 2)⁻¹.re =
      1 / (1 - r ^ 2) := by
    intro u
    have h1 : (ζ u) * (starRingEnd ℂ) (ζ u) = (1 : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ u]
      push_cast
      ring
    rw [h1, one_mul]
    have h2 : (1 : ℂ) - (r : ℂ) ^ 2 = ((1 - r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_inv, Complex.ofReal_re, inv_eq_one_div]
  -- Off-diagonal nonnegativity from re_one_sub_inv_nonneg.
  have h_off_nonneg : ∀ u v : Fin n,
      0 ≤ (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹.re := by
    intro u v
    apply re_one_sub_inv_nonneg
    have hzz : ‖(ζ u) * (starRingEnd ℂ) (ζ v)‖ = 1 := by
      rw [norm_mul, hζ u, Complex.norm_conj, hζ v, mul_one]
    rw [norm_mul, hzz, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, one_mul]
    nlinarith
  -- Goal: n²/2 + n/(2(1-r²)) ≤ Σ_{u,v} (1/2 + (1/2) Re(...)).
  -- Bound each pair: u=v contributes 1/2 + 1/(2(1-r²)); u≠v contributes ≥ 1/2.
  have h1mr_pos : 0 < 1 - r ^ 2 := by nlinarith
  -- Pointwise lower bound on each summand: indicate diagonal vs off-diagonal contribution.
  have h_pair_lb : ∀ u v : Fin n,
      (if u = v then ((1 : ℝ) / 2 + 1 / (2 * (1 - r ^ 2))) else (1 / 2 : ℝ)) ≤
        1 / 2 + (1 / 2) * (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹.re := by
    intro u v
    by_cases huv : u = v
    · rw [if_pos huv]
      subst huv
      rw [h_diag_eq]
      have h1mr_ne : (1 - r ^ 2 : ℝ) ≠ 0 := ne_of_gt h1mr_pos
      have : (1 : ℝ) / 2 + 1 / 2 * (1 / (1 - r ^ 2)) = 1 / 2 + 1 / (2 * (1 - r ^ 2)) := by
        field_simp
      linarith
    · rw [if_neg huv]
      have := h_off_nonneg u v
      linarith
  -- Sum the lower bounds.
  have h_sum_lb : ∑ u : Fin n, ∑ v : Fin n,
      (if u = v then ((1 : ℝ) / 2 + 1 / (2 * (1 - r ^ 2))) else (1 / 2 : ℝ)) ≤
      ∑ u : Fin n, ∑ v : Fin n,
        (1 / 2 + (1 / 2) * (1 - (ζ u) * (starRingEnd ℂ) (ζ v) * (r : ℂ) ^ 2)⁻¹.re) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact h_pair_lb u v
  refine le_trans ?_ h_sum_lb
  -- Compute Σ_{u,v} (if u=v then A else B) = n·A + n(n-1)·B for A = 1/2 + 1/(2(1-r²)), B = 1/2.
  -- = n·(1/2 + 1/(2(1-r²))) + n(n-1)·(1/2) = n/2 + n/(2(1-r²)) + n²/2 - n/2 = n²/2 + n/(2(1-r²)).
  have h_inner : ∀ u : Fin n, ∑ v : Fin n,
      (if u = v then ((1 : ℝ) / 2 + 1 / (2 * (1 - r ^ 2))) else (1 / 2 : ℝ)) =
        ((1 : ℝ) / 2 + 1 / (2 * (1 - r ^ 2))) + (n - 1 : ℕ) * (1 / 2) := by
    intro u
    rw [show (Finset.univ : Finset (Fin n)) = insert u (Finset.univ.erase u) by
      simp [Finset.insert_erase (Finset.mem_univ u)]]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
    rw [if_pos rfl]
    congr 1
    rw [Finset.sum_ite_of_false (fun v hv h_eq => (Finset.mem_erase.mp hv).1 h_eq.symm)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
  simp_rw [h_inner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  -- Goal: n²/2 + n/(2(1-r²)) ≤ n · (1/2 + 1/(2(1-r²)) + (n-1) · (1/2))
  -- RHS = n/2 + n/(2(1-r²)) + n(n-1)/2 = n²/2 + n/(2(1-r²))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    simp
  rw [hnm1]
  -- Goal: n²/2 + n/(2(1-r²)) ≤ n · (1/2 + 1/(2(1-r²)) + (n - 1) · (1/2))
  -- Both sides equal n²/2 + n/(2(1-r²)).
  have h_eq : (n : ℝ) * (1 / 2 + 1 / (2 * (1 - r ^ 2)) + ((n : ℝ) - 1) * (1 / 2)) =
      (n : ℝ) ^ 2 / 2 + (n : ℝ) / (2 * (1 - r ^ 2)) := by
    field_simp
    ring
  linarith

/-- **Clunie's Lemma 1 (Parseval inequality)** [Cl67]. For any $\zeta_1,\ldots,\zeta_n$ on
the unit circle and $0 \le r < 1$,
$$ n^2 + \sum_{k=1}^\infty |s_k|^2 r^{2k} \;\ge\; \tfrac{n^2}{2} + \tfrac{n}{2(1-r^2)} $$
where $s_k = \sum_v \zeta_v^k$.

This follows from `cluniePhi_normSq_integral` (Parseval form) and
`cluniePhi_normSq_integral_lower` (the $(\mathrm{Re}\,\varphi)^2$ lower bound). -/
@[category research solved, AMS 11 40 42]
theorem clunie_lemma_one {n : ℕ} (ζ : Fin n → ℂ) (hζ : ∀ v, ‖ζ v‖ = 1)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((n : ℝ) ^ 2 / 2 + (n : ℝ) / (2 * (1 - r ^ 2))) ≤
      (n : ℝ) ^ 2 + ∑' k : ℕ, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) := by
  rw [← cluniePhi_normSq_integral ζ hζ r hr0 hr1]
  exact cluniePhi_normSq_integral_lower ζ hζ r hr0 hr1

/- ## Clunie's `sqrt_lower_bound` proof: Lemma 2 (subset construction) and deduction -/

/-- **Block-sum bound from limsup.** If $A_v < \infty$, then for any $\varepsilon > 0$ there
is an $N(v, \varepsilon)$ such that any block-sum
$\sum_{j=N+1}^{N+n} e(v\,x_j)$ with $N+n \ge N(v, \varepsilon)$ and $N \ge N(v, \varepsilon)$
has norm at most $2 \cdot (A_v).\mathrm{toReal} + \varepsilon$.

*Proof.* From `Filter.eventually_lt_of_limsup_lt` applied to $A x v < (A x v)
.\mathrm{toReal} + \varepsilon/4$ (uses `hAfin`), we get $\forall^\infty n,\, \|\text{partial
sum}_n\| < (A x v).\mathrm{toReal} + \varepsilon/4$. Take $N$ from this eventually-clause; for
$N', m \ge N$, triangle inequality
$\|p_{N'} - p_m\| \le \|p_{N'}\| + \|p_m\| < 2(A_v).\mathrm{toReal} + \varepsilon/2 \le \cdots$. -/
@[category API, AMS 11]
theorem block_sum_bound_of_limsup_finite (x : ℕ → ℝ) (v : ℕ) (hAfin : A x v ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ m : ℕ, N ≤ m →
      ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖ ≤
        2 * (A x v).toReal + ε := by
  -- u n = (‖partial_n‖ : EReal); limsup u = A x v.
  set u : ℕ → EReal := fun n => ((‖∑ j ∈ range n, e ((v : ℝ) * x j)‖ : ℝ) : EReal) with hu_def
  have h_limsup : atTop.limsup u = A x v := rfl
  -- A x v < ((A x v).toReal + ε/4 : ℝ) cast to EReal.
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have h_lt_coe : A x v < (((A x v).toReal + ε / 4 : ℝ) : EReal) := by
    have h_le : A x v ≤ (((A x v).toReal : ℝ) : EReal) := EReal.le_coe_toReal hAfin
    have h_strict : (((A x v).toReal : ℝ) : EReal) < (((A x v).toReal + ε / 4 : ℝ) : EReal) := by
      exact_mod_cast (by linarith : (A x v).toReal < (A x v).toReal + ε / 4)
    exact lt_of_le_of_lt h_le h_strict
  -- Bounded above (any value works in EReal since EReal has top).
  have h_bdd : atTop.IsBoundedUnder (· ≤ ·) u :=
    ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
  -- Apply `Filter.eventually_lt_of_limsup_lt`.
  have h_ev : ∀ᶠ n : ℕ in atTop, u n < (((A x v).toReal + ε / 4 : ℝ) : EReal) :=
    Filter.eventually_lt_of_limsup_lt (h_limsup ▸ h_lt_coe) h_bdd
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N, hN⟩ := h_ev
  refine ⟨N, fun N' hN' m hm => ?_⟩
  -- Cast EReal bound to real bound.
  have h_cast : ∀ k, u k < (((A x v).toReal + ε / 4 : ℝ) : EReal) →
      ‖∑ j ∈ range k, e ((v : ℝ) * x j)‖ ≤ (A x v).toReal + ε / 4 := by
    intro k h
    show ‖∑ j ∈ range k, e ((v : ℝ) * x j)‖ ≤ (A x v).toReal + ε / 4
    have h' : ((‖∑ j ∈ range k, e ((v : ℝ) * x j)‖ : ℝ) : EReal) ≤
        (((A x v).toReal + ε / 4 : ℝ) : EReal) := h.le
    exact_mod_cast h'
  have hN'_R := h_cast N' (hN N' hN')
  have hm_R := h_cast m (hN m hm)
  calc ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖
      ≤ ‖∑ j ∈ range N', e ((v : ℝ) * x j)‖ + ‖∑ j ∈ range m, e ((v : ℝ) * x j)‖ :=
        norm_sub_le _ _
    _ ≤ ((A x v).toReal + ε / 4) + ((A x v).toReal + ε / 4) := by linarith
    _ ≤ 2 * (A x v).toReal + ε := by linarith

/-- **Strict block-sum bound from limsup < B.** If $A_v < B$ (where $B \in \mathbb{R}$), then
for some $N$, all blocks $\sum_{m_1+1}^{m_2} e(v \cdot x_k)$ with $m_1, m_2 \ge N$ have norm
$< 2B$ (strictly). This is Clunie's strict bound used in his Lemma 2. -/
@[category API, AMS 11]
theorem block_sum_bound_of_limsup_lt (x : ℕ → ℝ) (v : ℕ) (B : ℝ)
    (hB : A x v < ((B : ℝ) : EReal)) :
    ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ m : ℕ, N ≤ m →
      ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖ < 2 * B := by
  -- A x v ≠ ⊤ since A x v < B (real coercion is below ⊤).
  have hAfin : A x v ≠ ⊤ := by
    intro h
    rw [h] at hB
    exact absurd hB (not_lt.mpr le_top)
  -- A x v ≠ ⊥ since A x v ≥ 0 (limsup of nonneg).
  have hA_nonneg : (0 : EReal) ≤ A x v := by
    unfold A
    refine Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall ?_)
      ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
    intro k
    exact_mod_cast (norm_nonneg _)
  have hA_ne_bot : A x v ≠ ⊥ := fun hbot => by
    rw [hbot] at hA_nonneg; exact absurd hA_nonneg (by decide)
  -- (A x v).toReal < B.
  have hA_real_lt : (A x v).toReal < B := by
    have h_le : ((A x v).toReal : EReal) ≤ A x v := EReal.coe_toReal_le hA_ne_bot
    have h_lt : ((A x v).toReal : EReal) < ((B : ℝ) : EReal) := lt_of_le_of_lt h_le hB
    exact_mod_cast h_lt
  -- Apply block_sum_bound_of_limsup_finite with ε := (B - (A x v).toReal) / 2.
  set ε : ℝ := (B - (A x v).toReal) / 2 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨N, hN⟩ := block_sum_bound_of_limsup_finite x v hAfin hε_pos
  refine ⟨N, fun N' hN' m hm => ?_⟩
  have h := hN N' hN' m hm
  -- h : ‖block‖ ≤ 2*(A x v).toReal + ε. Show < 2*B.
  have h_bound : 2 * (A x v).toReal + ε < 2 * B := by rw [hε_def]; linarith
  linarith

/-- **Clunie's Lemma 2 (strict version).** Faithful Lean rendering of Clunie's [Cl67] Lemma 2
exactly as stated:

Given $A_v < \sqrt{v}$ for $v > k_1$ (which follows from $\limsup A_v/\sqrt v < c < 1$, taking
$c = 1$) and $\forall^\infty v,\ A_v \le c\sqrt{v}$, there exist integers $k_1 \le k_2$ such
that for any $n$ with $n^2 > k_2$ we can pick $\zeta : \mathrm{Fin}\,n \to \mathbb{C}$ from
$\{e(x_v)\}$ satisfying:
- $\|s_v(\zeta)\| < 2\sqrt v$ for $k_1 < v \le k_2$ (strict),
- $\|s_v(\zeta)\| < 2c\sqrt v$ for $k_2 < v \le n^2$ (strict).

Same Cesàro construction as the looser dual version, but uses
`block_sum_bound_of_limsup_lt` to get strict bounds matching Clunie's exactly. -/
@[category API, AMS 11 40 42]
theorem clunie_lemma_two_strict (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1)
    (k₁ : ℕ) (hk₁_strict : ∀ v : ℕ, k₁ < v → A x v < ((Real.sqrt v : ℝ) : EReal))
    (c : ℝ) (_hc : 0 < c) (_hc1 : c < 1)
    (hA : ∀ᶠ v : ℕ in atTop, A x v < ((c * Real.sqrt v : ℝ) : EReal)) :
    ∃ k₂ : ℕ, k₁ ≤ k₂ ∧ ∀ n : ℕ, k₂ < n ^ 2 →
      ∃ ζ : Fin n → ℂ, (∀ j, ‖ζ j‖ = 1) ∧
        (∀ j, ζ j ∈ (Set.range (fun k : ℕ => e (x k)))) ∧
        (∀ v : ℕ, k₁ < v → v ≤ k₂ → ‖clunieS ζ v‖ < 2 * Real.sqrt v) ∧
        (∀ v : ℕ, k₂ < v → v ≤ n ^ 2 → ‖clunieS ζ v‖ < 2 * c * Real.sqrt v) := by
  rw [Filter.eventually_atTop] at hA
  obtain ⟨k₂', hk₂'⟩ := hA
  let k₂ := max k₁ k₂'
  refine ⟨k₂, le_max_left _ _, fun n hn => ?_⟩
  -- For each v > k₁, pick N(v) using block_sum_bound_of_limsup_lt with B = √v (middle) or c√v (outer).
  have h_get_N_mid : ∀ v : ℕ, k₁ < v → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ m : ℕ, N ≤ m →
      ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖ <
        2 * Real.sqrt v :=
    fun v hv => block_sum_bound_of_limsup_lt x v _ (hk₁_strict v hv)
  have h_get_N_out : ∀ v : ℕ, k₂' ≤ v → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ m : ℕ, N ≤ m →
      ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖ <
        2 * (c * Real.sqrt v) :=
    fun v hv => block_sum_bound_of_limsup_lt x v _ (hk₂' v hv)
  classical
  let Nfun : ℕ → ℕ := fun v =>
    if hv : k₁ < v ∧ v ≤ n ^ 2 then
      if hk : k₂' ≤ v then Classical.choose (h_get_N_out v hk)
      else Classical.choose (h_get_N_mid v hv.1)
    else 0
  let S : Finset ℕ := (Finset.Ioc k₁ (n ^ 2))
  let N : ℕ := S.sup Nfun
  refine ⟨fun j : Fin n => e (x (N + j.val + 1)), ?_, ?_, ?_, ?_⟩
  · intro j; exact norm_e _
  · intro j; exact ⟨N + j.val + 1, rfl⟩
  · -- Middle range bound: k₁ < v ≤ k₂.
    intro v hv hv'
    have hv'' : v ≤ n ^ 2 := hv'.trans hn.le
    have hvS : v ∈ S := by rw [Finset.mem_Ioc]; exact ⟨hv, hv''⟩
    have hN_ge : Nfun v ≤ N := Finset.le_sup (f := Nfun) hvS
    -- Goal: ‖clunieS ζ v‖ < 2·√v.
    -- For middle range, v could be < k₂' or ≥ k₂'. Use mid bound (which always works for v > k₁).
    -- But Nfun selects either mid or out depending on v ≥ k₂'. Both bound by ≤ outer ≤ middle.
    -- Outer bound: 2c√v < 2·1·√v = 2√v (since c < 1, but here we don't have hc1 in scope... wait it's in let).
    -- We have c < 1 as hypothesis. So 2c√v < 2√v.
    -- But the bound from block_sum_bound_of_limsup_lt with B = c√v gives < 2c√v < 2√v. So either way < 2√v.
    by_cases hvk₂' : k₂' ≤ v
    · -- Use outer bound, then 2c√v < 2√v.
      have hv_pair : k₁ < v ∧ v ≤ n ^ 2 := ⟨hv, hv''⟩
      have hNfun_eq : Nfun v = Classical.choose (h_get_N_out v hvk₂') := by
        simp [Nfun, hv_pair, hvk₂']
      have hN_spec := Classical.choose_spec (h_get_N_out v hvk₂')
      have h_sum_eq : clunieS (fun j : Fin n => e (x (N + j.val + 1))) v =
          ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) := by
        unfold clunieS
        rw [show (fun j : Fin n => e (x (N + j.val + 1)) ^ v) =
            (fun i : Fin n => (fun j : ℕ => e (x (N + j + 1)) ^ v) i.val) from rfl]
        rw [Fin.sum_univ_eq_sum_range (fun j => e (x (N + j + 1)) ^ v)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [e_pow_eq]
      rw [h_sum_eq]
      have h_block : ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) =
          ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) -
            ∑ j ∈ range (N + 1), e ((v : ℝ) * x j) := by
        have h_split : ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) =
            (∑ j ∈ range (N + 1), e ((v : ℝ) * x j)) +
            ∑ j ∈ range n, e ((v : ℝ) * x (N + 1 + j)) := by
          rw [show N + n + 1 = (N + 1) + n by ring, Finset.sum_range_add]
        rw [h_split]
        have : ∀ j, N + 1 + j = N + j + 1 := fun j => by ring
        simp_rw [this]
        ring
      rw [h_block]
      have hN_le_Nn : Classical.choose (h_get_N_out v hvk₂') ≤ N + n + 1 := by
        have h := hN_ge; rw [hNfun_eq] at h; omega
      have hN_le_N1 : Classical.choose (h_get_N_out v hvk₂') ≤ N + 1 := by
        have h := hN_ge; rw [hNfun_eq] at h; omega
      have h_bound := hN_spec (N + n + 1) hN_le_Nn (N + 1) hN_le_N1
      -- h_bound: ‖block‖ < 2·c·√v. Show < 2·√v.
      have hv_pos : 0 < (v : ℝ) := by
        have : 0 < v := Nat.pos_of_ne_zero (fun h => by omega)
        exact_mod_cast this
      have hsqrt_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv_pos
      have hc_lt_1 : 2 * c * Real.sqrt v < 2 * Real.sqrt v := by
        have h2sqrt_pos : 0 < 2 * Real.sqrt v := by positivity
        nlinarith
      linarith
    · -- Use middle bound directly.
      push_neg at hvk₂'
      have hv_pair : k₁ < v ∧ v ≤ n ^ 2 := ⟨hv, hv''⟩
      have hNfun_eq : Nfun v = Classical.choose (h_get_N_mid v hv) := by
        simp [Nfun, hv_pair, hvk₂'.not_ge]
      have hN_spec := Classical.choose_spec (h_get_N_mid v hv)
      have h_sum_eq : clunieS (fun j : Fin n => e (x (N + j.val + 1))) v =
          ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) := by
        unfold clunieS
        rw [show (fun j : Fin n => e (x (N + j.val + 1)) ^ v) =
            (fun i : Fin n => (fun j : ℕ => e (x (N + j + 1)) ^ v) i.val) from rfl]
        rw [Fin.sum_univ_eq_sum_range (fun j => e (x (N + j + 1)) ^ v)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [e_pow_eq]
      rw [h_sum_eq]
      have h_block : ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) =
          ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) -
            ∑ j ∈ range (N + 1), e ((v : ℝ) * x j) := by
        have h_split : ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) =
            (∑ j ∈ range (N + 1), e ((v : ℝ) * x j)) +
            ∑ j ∈ range n, e ((v : ℝ) * x (N + 1 + j)) := by
          rw [show N + n + 1 = (N + 1) + n by ring, Finset.sum_range_add]
        rw [h_split]
        have : ∀ j, N + 1 + j = N + j + 1 := fun j => by ring
        simp_rw [this]
        ring
      rw [h_block]
      have hN_le_Nn : Classical.choose (h_get_N_mid v hv) ≤ N + n + 1 := by
        have h := hN_ge; rw [hNfun_eq] at h; omega
      have hN_le_N1 : Classical.choose (h_get_N_mid v hv) ≤ N + 1 := by
        have h := hN_ge; rw [hNfun_eq] at h; omega
      exact hN_spec (N + n + 1) hN_le_Nn (N + 1) hN_le_N1
  · -- Outer range bound: k₂ < v ≤ n².
    intro v hv hv'
    have hv_k₁ : k₁ < v := lt_of_le_of_lt (le_max_left k₁ k₂') hv
    have hv_k₂' : k₂' ≤ v := le_of_lt (lt_of_le_of_lt (le_max_right k₁ k₂') hv)
    have hvS : v ∈ S := by rw [Finset.mem_Ioc]; exact ⟨hv_k₁, hv'⟩
    have hN_ge : Nfun v ≤ N := Finset.le_sup (f := Nfun) hvS
    have hv_pair : k₁ < v ∧ v ≤ n ^ 2 := ⟨hv_k₁, hv'⟩
    have hNfun_eq : Nfun v = Classical.choose (h_get_N_out v hv_k₂') := by
      simp [Nfun, hv_pair, hv_k₂']
    have hN_spec := Classical.choose_spec (h_get_N_out v hv_k₂')
    have h_sum_eq : clunieS (fun j : Fin n => e (x (N + j.val + 1))) v =
        ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) := by
      unfold clunieS
      rw [show (fun j : Fin n => e (x (N + j.val + 1)) ^ v) =
          (fun i : Fin n => (fun j : ℕ => e (x (N + j + 1)) ^ v) i.val) from rfl]
      rw [Fin.sum_univ_eq_sum_range (fun j => e (x (N + j + 1)) ^ v)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e_pow_eq]
    rw [h_sum_eq]
    have h_block : ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) =
        ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) -
          ∑ j ∈ range (N + 1), e ((v : ℝ) * x j) := by
      have h_split : ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) =
          (∑ j ∈ range (N + 1), e ((v : ℝ) * x j)) +
          ∑ j ∈ range n, e ((v : ℝ) * x (N + 1 + j)) := by
        rw [show N + n + 1 = (N + 1) + n by ring, Finset.sum_range_add]
      rw [h_split]
      have : ∀ j, N + 1 + j = N + j + 1 := fun j => by ring
      simp_rw [this]
      ring
    rw [h_block]
    have hN_le_Nn : Classical.choose (h_get_N_out v hv_k₂') ≤ N + n + 1 := by
      have h := hN_ge; rw [hNfun_eq] at h; omega
    have hN_le_N1 : Classical.choose (h_get_N_out v hv_k₂') ≤ N + 1 := by
      have h := hN_ge; rw [hNfun_eq] at h; omega
    have h_bound := hN_spec (N + n + 1) hN_le_Nn (N + 1) hN_le_N1
    -- h_bound : ‖block‖ < 2 * (c * √v). Goal: ‖block‖ < 2 * c * √v.
    show _ < 2 * c * Real.sqrt v
    have : 2 * (c * Real.sqrt v) = 2 * c * Real.sqrt v := by ring
    linarith

/-- **Clunie's Lemma 2 (dual-range version).** Faithful Lean rendering of Clunie's
[Cl67] Lemma 2 with both ranges:

Given the eventual hypothesis $A_v \le c\sqrt{v}$ (which forces $A_v < \infty$ eventually,
so a sequence-determined finiteness threshold $k_1$ exists, made explicit here as a
hypothesis `hk₁`), there exists $k_2 \ge k_1$ such that for any $n$ with $n^2 > k_2$ we can
pick $\zeta : \mathrm{Fin}\,n \to \mathbb{C}$ from $\{e(x_v)\}$ satisfying:
- $\|s_v(\zeta)\| \le 2(A x v)_{\mathrm{toReal}} + \varepsilon$ for $k_1 < v \le k_2$
  (Cesàro range; uses block-sum bound from the limsup definition of $A_v$),
- $\|s_v(\zeta)\| \le 2 c \sqrt{v} + \varepsilon$ for $k_2 < v \le n^2$ (uses the eventual
  $c\sqrt{v}$ bound).

The Cesàro middle range is essential for the `sqrt_lower_bound` deduction: it bounds the
$k_1 < v \le k_2$ contribution by a constant (independent of $n$), avoiding the loss
inherent in the trivial $\|s_v\| \le n$ bound. -/
@[category API, AMS 11 40 42]
theorem clunie_lemma_two_dual (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1)
    (k₁ : ℕ) (hk₁ : ∀ v : ℕ, k₁ < v → A x v ≠ ⊤)
    (c : ℝ) (_hc : 0 < c) (_hc1 : c < 1)
    (hA : ∀ᶠ v : ℕ in atTop, A x v ≤ ((c * Real.sqrt v : ℝ) : EReal))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k₂ : ℕ, k₁ ≤ k₂ ∧ ∀ n : ℕ, k₂ < n ^ 2 →
      ∃ ζ : Fin n → ℂ, (∀ j, ‖ζ j‖ = 1) ∧
        (∀ j, ζ j ∈ (Set.range (fun k : ℕ => e (x k)))) ∧
        (∀ v : ℕ, k₁ < v → v ≤ k₂ →
          ‖clunieS ζ v‖ ≤ 2 * (A x v).toReal + ε) ∧
        (∀ v : ℕ, k₂ < v → v ≤ n ^ 2 →
          ‖clunieS ζ v‖ ≤ 2 * c * Real.sqrt v + ε) := by
  -- Take k₂' from the eventual hypothesis hA. Then set k₂ := max(k₁, k₂').
  rw [Filter.eventually_atTop] at hA
  obtain ⟨k₂', hk₂'⟩ := hA
  let k₂ := max k₁ k₂'
  refine ⟨k₂, le_max_left _ _, fun n hn => ?_⟩
  -- A x v finite for v > k₁ from hk₁, and for v > k₂ ≥ k₂' also from hA.
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h_get_N : ∀ v : ℕ, k₁ < v → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ m : ℕ, N ≤ m →
      ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖ ≤
        2 * (A x v).toReal + ε / 2 :=
    fun v hv => block_sum_bound_of_limsup_finite x v (hk₁ v hv) hε2
  classical
  let Nfun : ℕ → ℕ := fun v => if hv : k₁ < v ∧ v ≤ n ^ 2
    then Classical.choose (h_get_N v hv.1) else 0
  let S : Finset ℕ := (Finset.Ioc k₁ (n ^ 2))
  let N : ℕ := S.sup Nfun
  refine ⟨fun j : Fin n => e (x (N + j.val + 1)), ?_, ?_, ?_, ?_⟩
  · intro j; exact norm_e _
  · intro j; exact ⟨N + j.val + 1, rfl⟩
  · -- Middle range bound: k₁ < v ≤ k₂, use Cesàro.
    intro v hv hv'
    have hv'' : v ≤ n ^ 2 := hv'.trans hn.le
    have hvS : v ∈ S := by rw [Finset.mem_Ioc]; exact ⟨hv, hv''⟩
    have hN_ge : Nfun v ≤ N := Finset.le_sup (f := Nfun) hvS
    have hv_pair : k₁ < v ∧ v ≤ n ^ 2 := ⟨hv, hv''⟩
    have hNfun_eq : Nfun v = Classical.choose (h_get_N v hv) := by
      simp [Nfun, hv_pair]
    have hN_spec := Classical.choose_spec (h_get_N v hv)
    -- ‖clunieS ζ v‖ = ‖Σ_{j<n} e(v·x_{N+j+1})‖ = ‖partial_{N+n+1} - partial_{N+1}‖.
    have h_sum_eq : clunieS (fun j : Fin n => e (x (N + j.val + 1))) v =
        ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) := by
      unfold clunieS
      rw [show (fun j : Fin n => e (x (N + j.val + 1)) ^ v) =
          (fun i : Fin n => (fun j : ℕ => e (x (N + j + 1)) ^ v) i.val) from rfl]
      rw [Fin.sum_univ_eq_sum_range (fun j => e (x (N + j + 1)) ^ v)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e_pow_eq]
    rw [h_sum_eq]
    have h_block : ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) =
        ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) -
          ∑ j ∈ range (N + 1), e ((v : ℝ) * x j) := by
      have h_split : ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) =
          (∑ j ∈ range (N + 1), e ((v : ℝ) * x j)) +
          ∑ j ∈ range n, e ((v : ℝ) * x (N + 1 + j)) := by
        rw [show N + n + 1 = (N + 1) + n by ring, Finset.sum_range_add]
      rw [h_split]
      have : ∀ j, N + 1 + j = N + j + 1 := fun j => by ring
      simp_rw [this]
      ring
    rw [h_block]
    have hN_le_Nn : Classical.choose (h_get_N v hv) ≤ N + n + 1 := by
      have h := hN_ge; rw [hNfun_eq] at h; omega
    have hN_le_N1 : Classical.choose (h_get_N v hv) ≤ N + 1 := by
      have h := hN_ge; rw [hNfun_eq] at h; omega
    have h_bound := hN_spec (N + n + 1) hN_le_Nn (N + 1) hN_le_N1
    linarith
  · -- Outer range bound: k₂ < v ≤ n², use c·√v.
    intro v hv hv'
    have hv_k₁ : k₁ < v := lt_of_le_of_lt (le_max_left k₁ k₂') hv
    have hv_k₂' : k₂' ≤ v := le_of_lt (lt_of_le_of_lt (le_max_right k₁ k₂') hv)
    have hvS : v ∈ S := by rw [Finset.mem_Ioc]; exact ⟨hv_k₁, hv'⟩
    have hN_ge : Nfun v ≤ N := Finset.le_sup (f := Nfun) hvS
    have hv_pair : k₁ < v ∧ v ≤ n ^ 2 := ⟨hv_k₁, hv'⟩
    have hNfun_eq : Nfun v = Classical.choose (h_get_N v hv_k₁) := by
      simp [Nfun, hv_pair]
    have hN_spec := Classical.choose_spec (h_get_N v hv_k₁)
    have h_sum_eq : clunieS (fun j : Fin n => e (x (N + j.val + 1))) v =
        ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) := by
      unfold clunieS
      rw [show (fun j : Fin n => e (x (N + j.val + 1)) ^ v) =
          (fun i : Fin n => (fun j : ℕ => e (x (N + j + 1)) ^ v) i.val) from rfl]
      rw [Fin.sum_univ_eq_sum_range (fun j => e (x (N + j + 1)) ^ v)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e_pow_eq]
    rw [h_sum_eq]
    have h_block : ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) =
        ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) -
          ∑ j ∈ range (N + 1), e ((v : ℝ) * x j) := by
      have h_split : ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) =
          (∑ j ∈ range (N + 1), e ((v : ℝ) * x j)) +
          ∑ j ∈ range n, e ((v : ℝ) * x (N + 1 + j)) := by
        rw [show N + n + 1 = (N + 1) + n by ring, Finset.sum_range_add]
      rw [h_split]
      have : ∀ j, N + 1 + j = N + j + 1 := fun j => by ring
      simp_rw [this]
      ring
    rw [h_block]
    have hN_le_Nn : Classical.choose (h_get_N v hv_k₁) ≤ N + n + 1 := by
      have h := hN_ge; rw [hNfun_eq] at h; omega
    have hN_le_N1 : Classical.choose (h_get_N v hv_k₁) ≤ N + 1 := by
      have h := hN_ge; rw [hNfun_eq] at h; omega
    have h_bound := hN_spec (N + n + 1) hN_le_Nn (N + 1) hN_le_N1
    have hA_le := hk₂' v hv_k₂'
    have hAfin_v : A x v ≠ ⊤ := hk₁ v hv_k₁
    have hA_nonneg : (0 : EReal) ≤ A x v := by
      unfold A
      refine Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall ?_)
        ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
      intro k
      exact_mod_cast (norm_nonneg _)
    have hA_ne_bot : A x v ≠ ⊥ := by
      intro hbot
      rw [hbot] at hA_nonneg
      exact absurd hA_nonneg (by decide)
    have hA_real : (A x v).toReal ≤ c * Real.sqrt v := by
      have h1 : ((A x v).toReal : EReal) ≤ ((c * Real.sqrt v : ℝ) : EReal) := by
        rw [EReal.coe_toReal hAfin_v hA_ne_bot]; exact hA_le
      exact_mod_cast h1
    linarith

@[category API, AMS 11 40 42]
theorem clunie_lemma_two (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1)
    (c : ℝ) (_hc : 0 < c) (_hc1 : c < 1)
    (hA : ∀ᶠ v : ℕ in atTop, A x v ≤ ((c * Real.sqrt v : ℝ) : EReal))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k₂ : ℕ, ∀ n : ℕ, k₂ < n ^ 2 →
      ∃ ζ : Fin n → ℂ, (∀ j, ‖ζ j‖ = 1) ∧
        (∀ j, ζ j ∈ (Set.range (fun k : ℕ => e (x k)))) ∧
        (∀ v : ℕ, k₂ < v → v ≤ n ^ 2 →
          ‖clunieS ζ v‖ ≤ 2 * c * Real.sqrt v + ε) := by
  -- Take k₂ from the eventual hypothesis hA.
  rw [Filter.eventually_atTop] at hA
  obtain ⟨k₂, hk₂⟩ := hA
  refine ⟨k₂, fun n hn => ?_⟩
  -- For each v in {k₂+1, ..., n²}, get a block-bound radius from limsup.
  -- A x v is finite for v > k₂ since A x v ≤ c·√v.
  have hAfin : ∀ v : ℕ, k₂ < v → A x v ≠ ⊤ := by
    intro v hv
    have h := hk₂ v hv.le
    intro h_top
    rw [h_top] at h
    -- h : ⊤ ≤ ((c * √v : ℝ) : EReal). But (c * √v : ℝ) < ⊤, contradiction.
    exact absurd (lt_of_le_of_lt h (EReal.coe_lt_top _)) (lt_irrefl _)
  -- For each v ∈ {k₂+1, ..., n²}, get N(v) such that
  -- ‖partial_N' - partial_m‖ ≤ 2·(A x v).toReal + (ε/2) for N', m ≥ N(v).
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h_get_N : ∀ v : ℕ, k₂ < v → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ m : ℕ, N ≤ m →
      ‖∑ j ∈ range N', e ((v : ℝ) * x j) - ∑ j ∈ range m, e ((v : ℝ) * x j)‖ ≤
        2 * (A x v).toReal + ε / 2 := by
    intro v hv
    exact block_sum_bound_of_limsup_finite x v (hAfin v hv) hε2
  -- Use Classical.choose to pick N(v) for each v (only need finite range).
  classical
  let Nfun : ℕ → ℕ := fun v => if hv : k₂ < v ∧ v ≤ n ^ 2
    then Classical.choose (h_get_N v hv.1) else 0
  -- Take N = max over v ∈ {k₂+1, ..., n²}.
  let S : Finset ℕ := (Finset.Ioc k₂ (n ^ 2))
  let N : ℕ := S.sup Nfun
  -- Define ζ_j := e(x_{N + j + 1}) for j ∈ Fin n.
  refine ⟨fun j : Fin n => e (x (N + j.val + 1)), ?_, ?_, ?_⟩
  · -- ‖ζ j‖ = 1 since e has unit norm.
    intro j; exact norm_e _
  · -- ζ j is in the range of (e ∘ x).
    intro j
    exact ⟨N + j.val + 1, rfl⟩
  · -- The block-sum bound.
    intro v hv hv'
    have hvS : v ∈ S := by
      rw [Finset.mem_Ioc]; exact ⟨hv, hv'⟩
    have hN_ge : Nfun v ≤ N := Finset.le_sup (f := Nfun) hvS
    have hv_pair : k₂ < v ∧ v ≤ n ^ 2 := ⟨hv, hv'⟩
    have hNfun_eq : Nfun v = Classical.choose (h_get_N v hv) := by
      simp [Nfun, hv_pair]
    have hN_spec := Classical.choose_spec (h_get_N v hv)
    -- ‖clunieS ζ v‖ = ‖Σ_{j<n} (e (x (N+j+1)))^v‖ = ‖Σ_{j<n} e (v · x (N+j+1))‖
    have h_sum_eq : clunieS (fun j : Fin n => e (x (N + j.val + 1))) v =
        ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) := by
      unfold clunieS
      rw [show (fun j : Fin n => e (x (N + j.val + 1)) ^ v) =
          (fun i : Fin n => (fun j : ℕ => e (x (N + j + 1)) ^ v) i.val) from rfl]
      rw [Fin.sum_univ_eq_sum_range (fun j => e (x (N + j + 1)) ^ v)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e_pow_eq]
    rw [h_sum_eq]
    -- ∑_{j<n} e(v · x_{N+j+1}) = partial_{N+n+1} - partial_{N+1}, where partial_k = Σ_{j<k} e(v · x_j).
    have h_block : ∑ j ∈ range n, e ((v : ℝ) * x (N + j + 1)) =
        ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) -
          ∑ j ∈ range (N + 1), e ((v : ℝ) * x j) := by
      have h_split : ∑ j ∈ range (N + n + 1), e ((v : ℝ) * x j) =
          (∑ j ∈ range (N + 1), e ((v : ℝ) * x j)) +
          ∑ j ∈ range n, e ((v : ℝ) * x (N + 1 + j)) := by
        rw [show N + n + 1 = (N + 1) + n by ring, Finset.sum_range_add]
      rw [h_split]
      have : ∀ j, N + 1 + j = N + j + 1 := fun j => by ring
      simp_rw [this]
      ring
    rw [h_block]
    -- Apply hN_spec with N' = N + n + 1, m = N + 1.
    have hN_le_Nn : Classical.choose (h_get_N v hv) ≤ N + n + 1 := by
      have h := hN_ge
      rw [hNfun_eq] at h
      omega
    have hN_le_N1 : Classical.choose (h_get_N v hv) ≤ N + 1 := by
      have h := hN_ge
      rw [hNfun_eq] at h
      omega
    have h_bound := hN_spec (N + n + 1) hN_le_Nn (N + 1) hN_le_N1
    -- h_bound: ‖partial_{N+n+1} - partial_{N+1}‖ ≤ 2·(A x v).toReal + ε/2
    -- Goal: ‖partial_{N+n+1} - partial_{N+1}‖ ≤ 2·c·√v + ε
    -- Use A x v ≤ c·√v from hk₂.
    have hA_le := hk₂ v hv.le
    have hA_real : (A x v).toReal ≤ c * Real.sqrt v := by
      have hAfin_v := hAfin v hv
      have hA_nonneg : (0 : EReal) ≤ A x v := by
        unfold A
        refine Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall ?_)
          ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
        intro k
        exact_mod_cast (norm_nonneg _)
      have hA_ne_bot : A x v ≠ ⊥ := by
        intro hbot
        rw [hbot] at hA_nonneg
        exact absurd hA_nonneg (by decide)
      have h1 : ((A x v).toReal : EReal) ≤ ((c * Real.sqrt v : ℝ) : EReal) := by
        rw [EReal.coe_toReal hAfin_v hA_ne_bot]
        exact hA_le
      exact_mod_cast h1
    linarith

/-- **Range C bound (outer range) for Clunie's `sqrt_lower_bound`.**

Given a unit-modulus sequence $\zeta_v$ on the disk with the strict bound
$\|s_v\| < 2c\sqrt v$ for $k_2 < v \le M$ (from Lemma 2's outer-range bound),
the finite sum on the outer range is controlled by the geometric tsum
$\sum_v v \cdot (r^2)^v = r^2/(1-r^2)^2$:
$$ \sum_{k = k_2}^{M-1} \|s_{k+1}\|^2 r^{2(k+1)}
   \;<\; \sum_{v=1}^\infty 4 c^2 \cdot v \cdot (r^2)^v
   \;\le\; \frac{4 c^2}{(1-r^2)^2}. $$
This is the heaviest individual computation in Clunie's deduction; extracting it
into its own lemma keeps `sqrt_lower_bound` from blowing past the heartbeat budget. -/
@[category API, AMS 11 40 42]
private lemma clunie_range_C_bound {n : ℕ} (ζ : Fin n → ℂ)
    (k₂ M : ℕ) {c : ℝ} (hc_pos : 0 < c)
    {r : ℝ} (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (hζ_outer : ∀ v, k₂ < v → v ≤ M → ‖clunieS ζ v‖ < 2 * c * Real.sqrt v) :
    ∑ k ∈ Finset.Ico k₂ M, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
    4 * c ^ 2 / (1 - r ^ 2) ^ 2 := by
  have hr_sq_nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg _
  have hr_sq_lt : r ^ 2 < 1 := by
    have hr_lt_sq : r ^ 2 < 1 ^ 2 := by
      apply sq_lt_sq' _ hr_lt_one
      linarith
    simpa using hr_lt_sq
  have h_one_sub_pos : 0 < 1 - r ^ 2 := by linarith
  have hr_sq_norm_lt : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_sq_nn]; exact hr_sq_lt
  have h_tsum_v_r2v : (∑' v : ℕ, (v : ℝ) * (r ^ 2) ^ v) = r ^ 2 / (1 - r ^ 2) ^ 2 := by
    have := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr_sq_norm_lt
    convert this using 1
  have h_summable_v_r2v : Summable (fun v : ℕ => (v : ℝ) * (r ^ 2) ^ v) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr_sq_norm_lt).summable
  -- Per-term bound: each summand ≤ 4c²·(k+1)·(r²)^(k+1).
  have h_term : ∀ k ∈ Finset.Ico k₂ M,
      ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
      4 * c ^ 2 * ((k + 1 : ℕ) : ℝ) * (r ^ 2) ^ (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk_ge, hk_lt⟩ := hk
    have hv_gt : k₂ < k + 1 := by omega
    have hv_le : k + 1 ≤ M := hk_lt
    have h_strict := hζ_outer (k + 1) hv_gt hv_le
    have h_strict' : ‖clunieS ζ (k + 1)‖ < 2 * c * Real.sqrt ((k : ℝ) + 1) := by
      convert h_strict using 2
      push_cast; ring
    have hkp1_nn : (0 : ℝ) ≤ ((k : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
      linarith
    have h_2c_sqrt_nn : 0 ≤ 2 * c * Real.sqrt ((k : ℝ) + 1) := by positivity
    have h_norm_nn : 0 ≤ ‖clunieS ζ (k + 1)‖ := norm_nonneg _
    have h_sq_lt : ‖clunieS ζ (k + 1)‖ ^ 2 < (2 * c * Real.sqrt ((k : ℝ) + 1)) ^ 2 := by
      apply sq_lt_sq' _ h_strict'
      linarith
    have h_sq_eq : (2 * c * Real.sqrt ((k : ℝ) + 1)) ^ 2 = 4 * c ^ 2 * ((k : ℝ) + 1) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hkp1_nn]; ring
    have h_pow_eq : r ^ (2 * (k + 1)) = (r ^ 2) ^ (k + 1) := by ring
    rw [h_pow_eq]
    have h_pow_nn : 0 ≤ (r ^ 2) ^ (k + 1) := pow_nonneg hr_sq_nn _
    have h1 : ‖clunieS ζ (k + 1)‖ ^ 2 * (r ^ 2) ^ (k + 1) ≤
        (2 * c * Real.sqrt ((k : ℝ) + 1)) ^ 2 * (r ^ 2) ^ (k + 1) :=
      mul_le_mul_of_nonneg_right h_sq_lt.le h_pow_nn
    rw [h_sq_eq] at h1
    have h_cast : ((k + 1 : ℕ) : ℝ) = ((k : ℝ) + 1) := by push_cast; ring
    rw [h_cast]
    exact h1
  calc ∑ k ∈ Finset.Ico k₂ M,
          ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1))
      ≤ ∑ k ∈ Finset.Ico k₂ M, 4 * c ^ 2 * ((k + 1 : ℕ) : ℝ) * (r ^ 2) ^ (k + 1) := by
        apply Finset.sum_le_sum h_term
    _ ≤ ∑' v : ℕ, 4 * c ^ 2 * (v : ℝ) * (r ^ 2) ^ v := by
        have h_summable_full : Summable (fun v : ℕ => 4 * c ^ 2 * (v : ℝ) * (r ^ 2) ^ v) := by
          have := h_summable_v_r2v.mul_left (4 * c ^ 2)
          refine this.congr (fun n => ?_); ring
        have h_nn : ∀ v : ℕ, 0 ≤ 4 * c ^ 2 * (v : ℝ) * (r ^ 2) ^ v := fun v => by positivity
        set S' : Finset ℕ := (Finset.Ico k₂ M).image (· + 1)
        have h_inj : Set.InjOn (fun k : ℕ => k + 1) ↑(Finset.Ico k₂ M) :=
          fun a _ b _ h => Nat.succ_injective h
        have h_reindex : ∑ k ∈ Finset.Ico k₂ M,
            4 * c ^ 2 * ((k + 1 : ℕ) : ℝ) * (r ^ 2) ^ (k + 1) =
            ∑ v ∈ S', 4 * c ^ 2 * (v : ℝ) * (r ^ 2) ^ v := by
          show ∑ k ∈ _, _ = ∑ v ∈ ((Finset.Ico k₂ M).image (· + 1)), _
          rw [Finset.sum_image h_inj]
        rw [h_reindex]
        exact Summable.sum_le_tsum S' (fun i _ => h_nn i) h_summable_full
    _ = 4 * c ^ 2 * ∑' v : ℕ, (v : ℝ) * (r ^ 2) ^ v := by
        rw [show (fun v : ℕ => 4 * c ^ 2 * (v : ℝ) * (r ^ 2) ^ v) =
            (fun v : ℕ => 4 * c ^ 2 * ((v : ℝ) * (r ^ 2) ^ v)) by
          funext v; ring]
        rw [tsum_mul_left]
    _ = 4 * c ^ 2 * (r ^ 2 / (1 - r ^ 2) ^ 2) := by rw [h_tsum_v_r2v]
    _ ≤ 4 * c ^ 2 * (1 / (1 - r ^ 2) ^ 2) := by
        have h_pos : (0 : ℝ) < (1 - r ^ 2) ^ 2 := by positivity
        have h_le_one : r ^ 2 ≤ 1 := by linarith
        have h4c_nn : 0 ≤ 4 * c ^ 2 := by positivity
        apply mul_le_mul_of_nonneg_left _ h4c_nn
        apply div_le_div_of_nonneg_right h_le_one h_pos.le
    _ = 4 * c ^ 2 / (1 - r ^ 2) ^ 2 := by ring

/-- **Bernoulli decay bound** for Clunie's $r$.

If $r \ge 0$ and $r^2 = 1 - 1/(4(k_1+5)\,N_0)$, then
$r^{2N_0^2} \le \exp(-N_0/(4(k_1+5)))$ via `Real.one_sub_div_pow_le_exp_neg`. -/
@[category API, AMS 11 40 42]
private lemma clunie_r_pow_le_exp
    {k₁ N₀ : ℕ} (hN₀_pos : 0 < N₀)
    {r : ℝ}
    (hr_sq_eq : r ^ 2 = 1 - 1 / (4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ))) :
    r ^ (2 * N₀ ^ 2) ≤ Real.exp (-((N₀ : ℝ) / (4 * ((k₁ : ℝ) + 5)))) := by
  have hk₁_R_nn : (0 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4k5_pos : (0 : ℝ) < 4 * ((k₁ : ℝ) + 5) := by linarith
  have h4k5_ge_one : (1 : ℝ) ≤ 4 * ((k₁ : ℝ) + 5) := by linarith
  have hN₀R_pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀_pos
  have hN₀R_ge_one : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀_pos
  -- The Bernoulli ratio condition N/(4(k₁+5)) ≤ N².
  have h_t_le_n : (N₀ : ℝ) / (4 * ((k₁ : ℝ) + 5)) ≤ ((N₀ ^ 2 : ℕ) : ℝ) := by
    have hpush : ((N₀ ^ 2 : ℕ) : ℝ) = (N₀ : ℝ) ^ 2 := by push_cast; ring
    rw [hpush, div_le_iff₀ h4k5_pos]
    have hsq : (N₀ : ℝ) ≤ (N₀ : ℝ) ^ 2 := by rw [sq]; nlinarith [hN₀R_ge_one]
    calc (N₀ : ℝ) ≤ (N₀ : ℝ) ^ 2 := hsq
      _ = (N₀ : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (N₀ : ℝ) ^ 2 * (4 * ((k₁ : ℝ) + 5)) :=
          mul_le_mul_of_nonneg_left h4k5_ge_one (sq_nonneg _)
  -- Rewrite r^{2N₀²} as the Bernoulli expression.
  have h_eq : r ^ (2 * N₀ ^ 2) =
      (1 - (N₀ : ℝ) / (4 * ((k₁ : ℝ) + 5)) / ((N₀ ^ 2 : ℕ) : ℝ)) ^ N₀ ^ 2 := by
    rw [pow_mul, hr_sq_eq]
    congr 1
    have hN₀_ne : (N₀ : ℝ) ≠ 0 := ne_of_gt hN₀R_pos
    have h4k5_ne : (4 * ((k₁ : ℝ) + 5) : ℝ) ≠ 0 := ne_of_gt h4k5_pos
    push_cast
    field_simp
  rw [h_eq]; exact Real.one_sub_div_pow_le_exp_neg h_t_le_n

/-- **Polynomial bound on $\exp(-u)$**: from `Real.pow_div_factorial_le_exp` with $n = 3$,
for $u > 0$ we get $u^3/6 \le \exp(u)$, hence $\exp(-u) \le 6/u^3$. -/
@[category API, AMS 11 40 42]
private lemma exp_neg_le_six_div_pow_three {u : ℝ} (hu_pos : 0 < u) :
    Real.exp (-u) ≤ 6 / u ^ 3 := by
  have hu_nn : 0 ≤ u := hu_pos.le
  have h_pow_le_exp : u ^ 3 / 6 ≤ Real.exp u := by
    have h := Real.pow_div_factorial_le_exp u hu_nn 3
    have h_fact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h_fact] at h; exact h
  have hu3_div_pos : 0 < u ^ 3 / 6 := by positivity
  rw [Real.exp_neg]
  have h_inv := inv_anti₀ hu3_div_pos h_pow_le_exp
  have h_eq : (u ^ 3 / 6)⁻¹ = 6 / u ^ 3 := by
    rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm, ← div_eq_mul_inv]
  rw [← h_eq]; exact h_inv

/-- **Numerical-contradiction lemma**: if $N_0 \ge 100(k_1+5)^2$ and
$(9k_1{+}57.5)/25 \cdot N_0^2 \le 1536 (k_1{+}5)^4$ then `False`.
The strict gap is $23000 \cdot (k_1{+}5)^4 \le LHS$ vs $1536 \cdot (k_1{+}5)^4$ on the RHS. -/
@[category API, AMS 11 40 42]
private lemma clunie_numerical_contradiction
    {k₁ N₀ : ℕ} (hN₀_ge_big : 100 * (k₁ + 5) ^ 2 ≤ N₀)
    (h_final_chain :
      (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 ≤ 1536 * ((k₁ : ℝ) + 5) ^ 4) : False := by
  have hk₁_R_nn : (0 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_k5_pow4_pos : (0 : ℝ) < ((k₁ : ℝ) + 5) ^ 4 := by positivity
  -- N₀² ≥ 10000·(k₁+5)^4.
  have hN₀_R_sq : 10000 * ((k₁ : ℝ) + 5) ^ 4 ≤ (N₀ : ℝ) ^ 2 := by
    have h_lower : (100 : ℝ) * ((k₁ : ℝ) + 5) ^ 2 ≤ N₀ := by exact_mod_cast hN₀_ge_big
    nlinarith [h_lower, sq_nonneg ((k₁ : ℝ) + 5)]
  -- LHS ≥ (57.5/25)·10000·(k₁+5)^4 = 23000·(k₁+5)^4.
  have h_LHS_ge : (57.5 / 25 : ℝ) * (10000 * ((k₁ : ℝ) + 5) ^ 4) ≤
      (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 := by
    have h_factor1_le : (57.5 / 25 : ℝ) ≤ (9 * (k₁ : ℝ) + 57.5) / 25 := by
      have hk₁_nn : (0 : ℝ) ≤ 9 * (k₁ : ℝ) := by positivity
      linarith
    have h_factor2_nn : (0 : ℝ) ≤ 10000 * ((k₁ : ℝ) + 5) ^ 4 := by positivity
    have h_LHS_factor_nn : (0 : ℝ) ≤ (9 * (k₁ : ℝ) + 57.5) / 25 := by
      have : (0 : ℝ) ≤ 9 * (k₁ : ℝ) + 57.5 := by positivity
      positivity
    calc (57.5 / 25 : ℝ) * (10000 * ((k₁ : ℝ) + 5) ^ 4)
        ≤ (9 * (k₁ : ℝ) + 57.5) / 25 * (10000 * ((k₁ : ℝ) + 5) ^ 4) :=
          mul_le_mul_of_nonneg_right h_factor1_le h_factor2_nn
      _ ≤ (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hN₀_R_sq h_LHS_factor_nn
  -- 23000 > 1536, so LHS > 1536·(k₁+5)^4 — contradicts h_final_chain.
  have h_strict : 1536 * ((k₁ : ℝ) + 5) ^ 4 <
      (57.5 / 25 : ℝ) * (10000 * ((k₁ : ℝ) + 5) ^ 4) := by
    nlinarith [h_k5_pow4_pos]
  linarith

/-- **Final numerical contradiction step in Clunie's `sqrt_lower_bound` proof.**

After all the analytic work (Lemma 1 + Lemma 2 + 4-range tsum split + substitution of
$c^2 = 1/(100(k_1+5))$), Clunie's argument reduces to: under the choice
$r^2 = 1 - 1/(4(k_1+5)N_0)$ and $N_0 \ge 100(k_1+5)^2$, the inequality
$$ \tfrac{9k_1+57.5}{25} \cdot N_0^2 \;\le\; \tfrac{N_0^2 \cdot r^{2(N_0^2+1)}}{1 - r^2} $$
is impossible.

The contradiction comes from the polynomial bound $\exp(-u) \le 6/u^3$
(`Real.pow_div_factorial_le_exp` with $n=3$) combined with $r^{2N_0^2} \le \exp(-u)$
where $u := N_0/(4(k_1+5))$ (`Real.one_sub_div_pow_le_exp_neg`). Specifically the chain:
$$ \tfrac{9k_1+57.5}{25} \cdot N_0^2 \le 4(k_1{+}5) N_0^3 r^{2(N_0^2+1)}
   \le 4(k_1{+}5) N_0^3 \cdot \tfrac{6}{u^3} = 1536 (k_1{+}5)^4. $$
But $N_0^2 \ge 10000 (k_1{+}5)^4$, so the LHS is $\ge 23000 (k_1{+}5)^4$,
contradicting $\le 1536 (k_1{+}5)^4$. -/
@[category API, AMS 11 40 42]
private lemma clunie_exp_decay_contradiction
    {k₁ N₀ : ℕ} (hN₀_ge_big : 100 * (k₁ + 5) ^ 2 ≤ N₀)
    {r : ℝ} (hr_nn : 0 ≤ r) (hr_lt_one : r < 1)
    (hr_sq_eq : r ^ 2 = 1 - 1 / (4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ)))
    (h_clean_ineq :
      (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 ≤
        (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2)) : False := by
  -- Setup positivity facts.
  have hk₁_R_nn : (0 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast Nat.zero_le _
  have hk₁_5_pos : (0 : ℝ) < (k₁ : ℝ) + 5 := by linarith
  have h4k5_pos : (0 : ℝ) < 4 * ((k₁ : ℝ) + 5) := by linarith
  have hN₀_pos : 0 < N₀ := by
    have h_pos : 0 < 100 * (k₁ + 5) ^ 2 := by positivity
    omega
  have hN₀R_pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀_pos
  -- 1 - r² = 1/(4(k₁+5)·N₀); 1/(1-r²) = 4(k₁+5)·N₀.
  have h_one_sub_r_sq : 1 - r ^ 2 = 1 / (4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ)) := by linarith
  have h_one_sub_inv : (1 - r ^ 2)⁻¹ = 4 * ((k₁ : ℝ) + 5) * N₀ := by
    rw [h_one_sub_r_sq, one_div, inv_inv]
  -- Step 1: rewrite RHS as 4(k₁+5)·N₀³·r^{2(N₀²+1)}, get a chain inequality.
  have h_rhs_eq : (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) =
      4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 * r ^ (2 * (N₀ ^ 2 + 1)) := by
    rw [div_eq_mul_inv, h_one_sub_inv]; ring
  have h_chain1 : (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 ≤
      4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 * r ^ (2 * (N₀ ^ 2 + 1)) := by
    have h := h_clean_ineq; rw [h_rhs_eq] at h; exact h
  -- Step 2: r^{2(N₀²+1)} ≤ r^{2N₀²} ≤ exp(-u) via `clunie_r_pow_le_exp`.
  have h_r_pow_le : r ^ (2 * (N₀ ^ 2 + 1)) ≤ r ^ (2 * N₀ ^ 2) := by
    apply pow_le_pow_of_le_one hr_nn hr_lt_one.le; omega
  have h_exp_bound := clunie_r_pow_le_exp hN₀_pos hr_sq_eq
  -- Step 3: introduce u and bound exp(-u) ≤ 6/u³ via `exp_neg_le_six_div_pow_three`.
  set u : ℝ := (N₀ : ℝ) / (4 * ((k₁ : ℝ) + 5)) with hu_def
  have hu_pos : 0 < u := div_pos hN₀R_pos h4k5_pos
  have h_exp_inv := exp_neg_le_six_div_pow_three hu_pos
  -- Chain together: 4(k₁+5)·N₀³·r^{2(N₀²+1)} ≤ 4(k₁+5)·N₀³·(6/u³).
  have h_pos_coef : 0 ≤ 4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 := by positivity
  have h_combined_le : r ^ (2 * (N₀ ^ 2 + 1)) ≤ 6 / u ^ 3 := by
    have h_eq_neg : Real.exp (-((N₀ : ℝ) / (4 * ((k₁ : ℝ) + 5)))) = Real.exp (-u) := by
      rw [hu_def]
    calc r ^ (2 * (N₀ ^ 2 + 1)) ≤ r ^ (2 * N₀ ^ 2) := h_r_pow_le
      _ ≤ Real.exp (-((N₀ : ℝ) / (4 * ((k₁ : ℝ) + 5)))) := h_exp_bound
      _ = Real.exp (-u) := h_eq_neg
      _ ≤ 6 / u ^ 3 := h_exp_inv
  have h_chain2 : 4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 * r ^ (2 * (N₀ ^ 2 + 1)) ≤
      4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 * (6 / u ^ 3) :=
    mul_le_mul_of_nonneg_left h_combined_le h_pos_coef
  -- Algebraic simplification: 4(k₁+5)·N₀³·6/u³ = 1536·(k₁+5)^4.
  have h_simplify : 4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 * (6 / u ^ 3) =
      1536 * ((k₁ : ℝ) + 5) ^ 4 := by
    rw [hu_def]
    have h_ne : (4 * ((k₁ : ℝ) + 5)) ≠ 0 := ne_of_gt h4k5_pos
    have hN₀_ne : (N₀ : ℝ) ≠ 0 := ne_of_gt hN₀R_pos
    field_simp; ring
  -- Combined chain: (9k₁+57.5)/25 · N₀² ≤ 1536·(k₁+5)^4.
  have h_final_chain :
      (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 ≤ 1536 * ((k₁ : ℝ) + 5) ^ 4 := by
    have h := h_chain1.trans h_chain2; rw [h_simplify] at h; exact h
  -- Numerical contradiction via `clunie_numerical_contradiction`.
  exact clunie_numerical_contradiction hN₀_ge_big h_final_chain

/-- Clunie [Cl67] proved that, for every infinite sequence $x_1, x_2, \ldots \in (0, 1)$,
$A_k \gg k^{1/2}$ for infinitely many $k$. (Tao independently found a proof.)

**Proof outline (Clunie 1967).** Set $\zeta_v = e(x_v)$ on the unit circle and
$s_k = \sum_{v=1}^n \zeta_v^k$. Argue by contradiction: assume
$\limsup_v A_v / \sqrt{v} \le c$ for some $c < 1/(8\sqrt{k_1+5})$, where $k_1$ is the integer
from Lemma 2 below.

*Lemma 1 (Parseval inequality).* `clunie_lemma_one`:
$$ n^2 + \sum_{k=1}^\infty |s_k|^2 r^{2k} \;\ge\; \tfrac{n^2}{2} + \tfrac{n}{2(1-r^2)}. $$

*Lemma 2 (subset construction).* Under the contradiction hypothesis, there exist integers
$k_1 \le k_2$ (with $k_1$ depending only on $\{x_v\}$) such that for any $n$ with $n^2 > k_2$
we can pick $\zeta_1,\ldots,\zeta_n$ from $\{e(x_v)\}$ with
$|s_v| < 2\sqrt v$ for $k_1 < v \le k_2$ and $|s_v| < 2 c\sqrt{v}$ for $k_2 < v \le n^2$
(strict bounds, via `clunie_lemma_two_strict`).

*Deduction.* Choose $r$ with $1/(1-r^2) = 4(k_1+5) N_0$ where $N_0 = \max(k_2{+}1,\ 100(k_1{+}5)^2)$.
Lemma 1's lower bound is then of order $(k_1{+}5) N_0^2$; bounding the right side by trivial
estimates ($\|s_k\| \le N_0$) for $k \le k_1$, by the strict Lemma 2 bounds for $k_1 < k \le N_0^2$,
and a geometric tail estimate for $k > N_0^2$, yields an upper bound of the form
$(k_1 + 4 + 64 c^2 (k_1{+}5)^2) N_0^2 + 4(k_1{+}5) N_0^3 r^{2(N_0^2+1)}$. Substituting
$c^2 = 1/(100(k_1{+}5))$ and applying `clunie_exp_decay_contradiction` (which uses
$\exp(-u) \le 6/u^3$ via `Real.pow_div_factorial_le_exp` together with $r^{2N_0^2} \le \exp(-u)$
for $u = N_0/(4(k_1{+}5))$) closes the contradiction numerically.

The final numerical contradiction is extracted into `clunie_exp_decay_contradiction`. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.sqrt_lower_bound
    (x : ℕ → ℝ) (hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c > 0, ∃ᶠ k : ℕ in atTop, ((c * Real.sqrt k : ℝ) : EReal) ≤ A x k := by
  -- Faithful Lean rendering of Clunie's [Cl67] proof.
  -- Proof by contradiction. Assume ¬ goal: ∀ c > 0, ∀ᶠ k, A x k < c·√k.
  by_contra h_neg
  push_neg at h_neg
  -- Step 1 (Clunie): from ∀c, ∀ᶠ v, A_v < c√v, applied with c=1: ∀ᶠ v, A_v < √v.
  -- This gives k₁ "depending only on the sequence" such that A_v < √v for v > k₁.
  have h1 := h_neg 1 (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at h1
  obtain ⟨k₁, hk₁_lt⟩ := h1
  -- hk₁_lt : ∀ v ≥ k₁, A x v < ((1 * √v : ℝ) : EReal) = ((√v : ℝ) : EReal).
  have hk₁_fin : ∀ v : ℕ, k₁ < v → A x v ≠ ⊤ := by
    intro v hv h_top
    have := hk₁_lt v hv.le
    rw [h_top] at this
    exact absurd (lt_trans this (EReal.coe_lt_top _)) (lt_irrefl _)
  -- Step 2 (Clunie): pick c < 1/(8·√(k₁+5)). Take c = 1/(10·√(k₁+5)).
  set c : ℝ := 1 / (10 * Real.sqrt ((k₁ : ℝ) + 5)) with hc_def
  have hsqrt_pos : 0 < Real.sqrt ((k₁ : ℝ) + 5) := Real.sqrt_pos.mpr (by positivity)
  have hc_pos : 0 < c := by
    rw [hc_def]; apply div_pos one_pos; positivity
  have hc_lt_one : c < 1 := by
    rw [hc_def]
    have h_lower : 1 ≤ Real.sqrt ((k₁ : ℝ) + 5) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      have h_nn : (0 : ℝ) ≤ (k₁ : ℝ) := by positivity
      linarith
    have hpos : 0 < 10 * Real.sqrt ((k₁ : ℝ) + 5) := by positivity
    rw [div_lt_one hpos]; linarith
  -- Step 3: Apply hypothesis with this c.
  have h_lt_c := h_neg c hc_pos
  have h_le_c : ∀ᶠ v : ℕ in atTop, A x v ≤ ((c * Real.sqrt v : ℝ) : EReal) :=
    h_lt_c.mono fun _ hk => hk.le
  -- Step 4: Apply dual-range Lemma 2.
  -- Convert hk₁_lt's "1 * √v" to "√v" for clunie_lemma_two_strict.
  have hk₁_strict : ∀ v : ℕ, k₁ < v → A x v < ((Real.sqrt v : ℝ) : EReal) := by
    intro v hv
    have h := hk₁_lt v hv.le
    rwa [show ((1 * Real.sqrt v : ℝ) : EReal) = ((Real.sqrt v : ℝ) : EReal) from by
      norm_num] at h
  obtain ⟨k₂, hk₁_le_k₂, hL2⟩ :=
    clunie_lemma_two_strict x hx k₁ hk₁_strict c hc_pos hc_lt_one h_lt_c
  -- Step 5 (Clunie's deduction): bound chain.
  -- Pick n large enough; apply Lemma 1 with r chosen so 1/(1-r²) = 4(k₁+5)n; bound chase.
  -- Now using clunie_lemma_two_strict with EXACT Clunie bounds:
  --   Middle (k₁ < v ≤ k₂): ‖s_v‖ < 2√v, so ‖s_v‖² < 4v.
  --   Outer  (k₂ < v ≤ N²): ‖s_v‖ < 2c√v, so ‖s_v‖² < 4c²v.
  --
  -- Bound chain (Clunie's exact constants):
  --   N²/2 + N/(2(1-r²)) ≤ N² + Σ |s_v|² r^{2v}  (Lemma 1)
  --   ⟹ Σ ≥ N/(2(1-r²)) - N²/2 = 2(k₁+5)N² - N²/2.
  --
  --   Σ ≤ k₁N² + 4Σ_{v=1}^{k₂} v + 4c²Σ_{v=0}^∞ v r^{2v} + N²·r^{2(N²+1)}/(1-r²)  [strict]
  --     ≤ k₁N² + 4k₂² + 4c²/(1-r²)² + 4(k₁+5)N³r^{2(N²+1)}
  --     ≤ (k₁+4)N² + 64c²(k₁+5)²N² + 4(k₁+5)N³r^{2(N²+1)}  [for N ≥ k₂].
  --
  --   Combined: 2(k₁+5)N² - N²/2 ≤ (k₁+4)N² + 64c²(k₁+5)²N² + 4(k₁+5)N³r^{2(N²+1)}.
  --   ⟹ (k₁+11/2)N² ≤ 64c²(k₁+5)²N² + 4(k₁+5)N³r^{2(N²+1)}.
  --   Divide by N²: (k₁+11/2) ≤ 64c²(k₁+5)² + 4(k₁+5)Nr^{2(N²+1)}.
  --
  -- For c² = 1/(100(k₁+5)): 64c²(k₁+5)² = 16(k₁+5)/25.
  --   (k₁+11/2) - 16(k₁+5)/25 = (25k₁+137.5 - 16k₁ - 80)/25 = (9k₁+57.5)/25 ≥ 57.5/25 = 2.3 > 0.
  -- So 2.3 ≤ tail/N² = 4(k₁+5)Nr^{2(N²+1)}.
  -- For N large: r^{2N²} = (1 - 1/(4(k₁+5)N))^{N²} ≤ exp(-N/(4(k₁+5))) → 0 super-poly.
  -- So tail/N² → 0, eventually < 2.3, contradicting the chain inequality.
  --
  -- Step (a): explicit N₀.
  set N₀ : ℕ := max (k₂ + 1) (100 * (k₁ + 5) ^ 2) with hN₀_def
  -- Properties of N₀:
  have hN₀_ge_k₂_plus : k₂ + 1 ≤ N₀ := le_max_left _ _
  have hN₀_ge : k₂ ≤ N₀ := by have := hN₀_ge_k₂_plus; omega
  have hN₀_lt_sq : k₂ < N₀ ^ 2 := by
    have h1 : N₀ ≥ 1 := by have := hN₀_ge_k₂_plus; omega
    have h2 : k₂ < N₀ := by have := hN₀_ge_k₂_plus; omega
    have : N₀ ≤ N₀ ^ 2 := by
      rw [sq]; exact Nat.le_mul_of_pos_left _ h1
    omega
  have hN₀_pos : 0 < N₀ := by have := hN₀_ge_k₂_plus; omega
  -- Condition (iii): 1 < 4(k₁+5)N₀ (so r ∈ (0, 1) well-defined).
  have hN₀_ge_big : 100 * (k₁ + 5) ^ 2 ≤ N₀ := le_max_right _ _
  -- Apply Lemma 2 to get ζ_N₀.
  obtain ⟨ζ, hζ_norm, _hζ_range, hζ_mid, hζ_outer⟩ := hL2 N₀ hN₀_lt_sq
  -- Define r² = 1 - 1/(4(k₁+5)N₀); needs 4(k₁+5)N₀ > 1 (positive denominator).
  have hk₅_pos : (0 : ℝ) < 4 * ((k₁ : ℝ) + 5) := by positivity
  have hN₀R_pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀_pos
  have hk₁_R_nn : (0 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast Nat.zero_le _
  have hk₁_5_pos : (0 : ℝ) < (k₁ : ℝ) + 5 := by linarith
  have h4k5_pos : (0 : ℝ) < 4 * ((k₁ : ℝ) + 5) := by linarith
  have h4k5N₀_pos : (0 : ℝ) < 4 * ((k₁ : ℝ) + 5) * N₀ := mul_pos h4k5_pos hN₀R_pos
  have h4k5_ge_20 : (20 : ℝ) ≤ 4 * ((k₁ : ℝ) + 5) := by linarith
  have hN₀R_ge_one : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀_pos
  have h4k5N₀_ge_one : 1 ≤ 4 * ((k₁ : ℝ) + 5) * N₀ := by
    calc 1 ≤ 20 * 1 := by norm_num
      _ ≤ (4 * ((k₁ : ℝ) + 5)) * N₀ := by
          apply mul_le_mul h4k5_ge_20 hN₀R_ge_one (by norm_num) (by linarith)
  -- r² = 1 - 1/(4(k₁+5)N₀) ∈ [0, 1).
  set r_sq : ℝ := 1 - 1 / (4 * ((k₁ : ℝ) + 5) * N₀) with hr_sq_def
  have hr_sq_lt_one : r_sq < 1 := by
    rw [hr_sq_def]
    have : 0 < 1 / (4 * ((k₁ : ℝ) + 5) * N₀) := by
      apply div_pos one_pos h4k5N₀_pos
    linarith
  have hr_sq_nn : 0 ≤ r_sq := by
    rw [hr_sq_def]
    have : 1 / (4 * ((k₁ : ℝ) + 5) * N₀) ≤ 1 := by
      rw [div_le_one h4k5N₀_pos]; exact h4k5N₀_ge_one
    linarith
  set r : ℝ := Real.sqrt r_sq with hr_def
  have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hr_sq_nn hr_sq_lt_one
  have hr_sq_eq : r ^ 2 = r_sq := by
    rw [hr_def, sq, ← Real.sqrt_mul hr_sq_nn, Real.sqrt_mul_self hr_sq_nn]
  -- 1/(1-r²) = 4(k₁+5)·N₀.
  have h_one_sub_r_sq : 1 - r ^ 2 = 1 / (4 * ((k₁ : ℝ) + 5) * N₀) := by
    rw [hr_sq_eq, hr_sq_def]
    ring
  -- Apply clunie_lemma_one to ζ.
  have h_lemma1 := clunie_lemma_one ζ hζ_norm r hr_nn hr_lt_one
  -- h_lemma1 : (N₀² / 2 + N₀ / (2(1-r²))) ≤ N₀² + ∑'_k ‖clunieS ζ (k+1)‖² · r^{2(k+1)}
  -- Substitute 1/(1-r²) = 4(k₁+5)·N₀ to derive a clean LHS lower bound.
  have h_one_sub_inv : (1 - r ^ 2)⁻¹ = 4 * ((k₁ : ℝ) + 5) * N₀ := by
    rw [h_one_sub_r_sq, one_div]
    rw [inv_inv]
  have h_lemma1' :
      ((N₀ : ℝ) ^ 2 / 2 + 2 * ((k₁ : ℝ) + 5) * N₀ ^ 2) ≤
      (N₀ : ℝ) ^ 2 + ∑' k : ℕ, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) := by
    have h_eq : (N₀ : ℝ) / (2 * (1 - r ^ 2)) = 2 * ((k₁ : ℝ) + 5) * N₀ ^ 2 := by
      rw [show (2 : ℝ) * (1 - r ^ 2) = 2 / (1 - r ^ 2)⁻¹ by
        rw [div_eq_mul_inv, inv_inv]]
      rw [h_one_sub_inv]
      have : (4 * ((k₁ : ℝ) + 5) * N₀ : ℝ) ≠ 0 := ne_of_gt h4k5N₀_pos
      field_simp
      ring
    linarith [h_lemma1, h_eq.symm.le]
  -- Each clunieS bound: trivially ‖s_v‖ ≤ N₀ for v ≥ 0.
  have h_norm_le : ∀ v : ℕ, ‖clunieS ζ v‖ ≤ (N₀ : ℝ) := norm_clunieS_le ζ hζ_norm
  have h_norm_sq_le : ∀ v : ℕ, ‖clunieS ζ v‖ ^ 2 ≤ (N₀ : ℝ) ^ 2 := by
    intro v
    have h := h_norm_le v
    have h_nn : 0 ≤ ‖clunieS ζ v‖ := norm_nonneg _
    rw [sq, sq]
    exact mul_le_mul h h h_nn (le_of_lt hN₀R_pos)
  -- Summability: ‖s_{k+1}‖² · r^{2(k+1)} ≤ N₀² · r^{2(k+1)}; the latter is geometric.
  have hr_sq_lt : r ^ 2 < 1 := by rw [hr_sq_eq]; exact hr_sq_lt_one
  have hr_sq_nn : (0 : ℝ) ≤ r ^ 2 := by rw [hr_sq_eq]; exact hr_sq_nn
  have h_summable : Summable (fun k : ℕ => ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1))) := by
    have h_geom : Summable (fun k : ℕ => (r ^ 2) ^ k) :=
      summable_geometric_of_lt_one hr_sq_nn hr_sq_lt
    have h_bd : Summable (fun k : ℕ => (N₀ : ℝ) ^ 2 * (r ^ 2) ^ (k + 1)) := by
      have := (h_geom.mul_left ((N₀ : ℝ) ^ 2 * r ^ 2))
      refine this.congr (fun n => ?_)
      rw [pow_succ]; ring
    refine h_bd.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    have h_eq : r ^ (2 * (k + 1)) = (r ^ 2) ^ (k + 1) := by ring
    rw [h_eq]
    have h_pow_nn : 0 ≤ (r ^ 2) ^ (k + 1) := pow_nonneg hr_sq_nn _
    exact mul_le_mul_of_nonneg_right (h_norm_sq_le _) h_pow_nn
  -- Split tsum at k = N₀² using Summable.sum_add_tsum_nat_add.
  have h_split := h_summable.sum_add_tsum_nat_add (N₀ ^ 2)
  -- h_split : ∑' k, f k = (Σ k ∈ range N₀², f k) + ∑' k, f (k + N₀²)
  -- Bound the tail (Range D): ∑' k, f(k + N₀²) ≤ N₀² · r^{2(N₀²+1)} / (1-r²).
  have h_tail_bound : ∑' k : ℕ, ‖clunieS ζ (k + N₀ ^ 2 + 1)‖ ^ 2 *
        r ^ (2 * (k + N₀ ^ 2 + 1)) ≤
      (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) := by
    -- Each term ≤ N₀² · r^{2(k + N₀² + 1)} = N₀² · r^{2(N₀²+1)} · (r²)^k.
    have h_term_le : ∀ k : ℕ, ‖clunieS ζ (k + N₀ ^ 2 + 1)‖ ^ 2 * r ^ (2 * (k + N₀ ^ 2 + 1)) ≤
        (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k := by
      intro k
      have h_pow_eq : r ^ (2 * (k + N₀ ^ 2 + 1)) = r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k := by
        rw [show 2 * (k + N₀ ^ 2 + 1) = 2 * (N₀ ^ 2 + 1) + 2 * k by ring, pow_add]
        congr 1; ring
      rw [h_pow_eq]
      have h_pow_nn : 0 ≤ r ^ (2 * (N₀ ^ 2 + 1)) := pow_nonneg hr_nn _
      have h_pow2_nn : 0 ≤ (r ^ 2) ^ k := pow_nonneg hr_sq_nn _
      have h_mul_nn : 0 ≤ r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k := mul_nonneg h_pow_nn h_pow2_nn
      have h_norm := h_norm_sq_le (k + N₀ ^ 2 + 1)
      have h_norm_nn : 0 ≤ ‖clunieS ζ (k + N₀ ^ 2 + 1)‖ ^ 2 := sq_nonneg _
      have h1 : ‖clunieS ζ (k + N₀ ^ 2 + 1)‖ ^ 2 *
          (r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k) ≤
          (N₀ : ℝ) ^ 2 * (r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k) :=
        mul_le_mul_of_nonneg_right h_norm h_mul_nn
      linarith
    -- Σ' bound by N₀² · r^{2(N₀²+1)} · Σ' (r²)^k = N₀² · r^{2(N₀²+1)} / (1-r²).
    have h_sum := tsum_geometric_of_lt_one hr_sq_nn hr_sq_lt
    -- h_sum : ∑' k, (r²)^k = (1 - r²)⁻¹
    have h_summable_geom : Summable (fun k : ℕ => (r ^ 2) ^ k) :=
      summable_geometric_of_lt_one hr_sq_nn hr_sq_lt
    have h_summable_scaled : Summable
        (fun k : ℕ => (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k) :=
      h_summable_geom.mul_left _
    have h_summable_lhs : Summable
        (fun k : ℕ => ‖clunieS ζ (k + N₀ ^ 2 + 1)‖ ^ 2 * r ^ (2 * (k + N₀ ^ 2 + 1))) := by
      have h_inj : Function.Injective (fun k : ℕ => k + N₀ ^ 2) :=
        fun a b h => Nat.add_right_cancel h
      have hcomp := h_summable.comp_injective h_inj
      refine hcomp.congr (fun n => ?_)
      show ‖clunieS ζ ((n + N₀ ^ 2) + 1)‖ ^ 2 * r ^ (2 * ((n + N₀ ^ 2) + 1)) =
        ‖clunieS ζ (n + N₀ ^ 2 + 1)‖ ^ 2 * r ^ (2 * (n + N₀ ^ 2 + 1))
      rfl
    calc ∑' k : ℕ, ‖clunieS ζ (k + N₀ ^ 2 + 1)‖ ^ 2 * r ^ (2 * (k + N₀ ^ 2 + 1))
        ≤ ∑' k : ℕ, (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) * (r ^ 2) ^ k :=
          Summable.tsum_le_tsum h_term_le h_summable_lhs h_summable_scaled
      _ = (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) * ∑' k : ℕ, (r ^ 2) ^ k :=
          tsum_mul_left
      _ = (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) * (1 - r ^ 2)⁻¹ := by rw [h_sum]
      _ = (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) := by
          rw [div_eq_mul_inv]
  -- Bound the finite prefix sum Σ_{k ∈ range N₀²} ‖s_{k+1}‖² · r^{2(k+1)}.
  -- Term-wise bound: each term ≤ N₀² (using h_norm_sq_le and r^{2v} ≤ 1).
  have hr_2_le_one : ∀ k : ℕ, r ^ (2 * (k + 1)) ≤ 1 := by
    intro k
    apply pow_le_one₀ hr_nn hr_lt_one.le
  -- Trivial bound on the finite prefix: Σ ≤ k₁ · N₀² + (range B contribution) + (range C contribution).
  -- For now, use trivial uniform bound on entire finite sum: Σ ≤ N₀² · (geometric sum bounded by 1/(1-r²)).
  -- Actually, we'll use the sharper 4-range bound. For Range A (v ≤ k₁):
  have h_range_A : ∑ k ∈ Finset.range k₁, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
      (k₁ : ℝ) * (N₀ : ℝ) ^ 2 := by
    calc ∑ k ∈ Finset.range k₁, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1))
        ≤ ∑ k ∈ Finset.range k₁, (N₀ : ℝ) ^ 2 * 1 := by
          apply Finset.sum_le_sum
          intro k _
          have h_sq := h_norm_sq_le (k + 1)
          have h_r := hr_2_le_one k
          have h_r_nn : 0 ≤ r ^ (2 * (k + 1)) := pow_nonneg hr_nn _
          have h_norm_nn : 0 ≤ ‖clunieS ζ (k + 1)‖ ^ 2 := sq_nonneg _
          have hN_nn : 0 ≤ (N₀ : ℝ) ^ 2 := sq_nonneg _
          have h_step1 : ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
              (N₀ : ℝ) ^ 2 * r ^ (2 * (k + 1)) :=
            mul_le_mul_of_nonneg_right h_sq h_r_nn
          have h_step2 : (N₀ : ℝ) ^ 2 * r ^ (2 * (k + 1)) ≤ (N₀ : ℝ) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left h_r hN_nn
          linarith
      _ = k₁ * (N₀ : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, mul_one]
          rw [nsmul_eq_mul]
  -- Range B (k ∈ Ico k₁ k₂, v = k+1 ∈ {k₁+1, ..., k₂}): ‖s_v‖² < 4v ≤ 4·k₂.
  -- Need k₂ ≤ N₀² (for Ico to be a subset of range N₀²). We have hN₀_lt_sq : k₂ < N₀².
  -- Note: hk₁_le_k₂ : k₁ ≤ k₂.
  have hN₀_ge_k₂_R : (k₂ : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀_ge
  have h_range_B : ∑ k ∈ Finset.Ico k₁ k₂, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
      4 * (N₀ : ℝ) ^ 2 := by
    calc ∑ k ∈ Finset.Ico k₁ k₂, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1))
        ≤ ∑ k ∈ Finset.Ico k₁ k₂, 4 * (N₀ : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Ico] at hk
          obtain ⟨hk_ge, hk_lt⟩ := hk
          have hv_gt : k₁ < k + 1 := by omega
          have hv_le : k + 1 ≤ k₂ := hk_lt
          have h_strict := hζ_mid (k + 1) hv_gt hv_le
          have h_sqrt_nn : 0 ≤ Real.sqrt (k + 1) := Real.sqrt_nonneg _
          have h_norm_nn : 0 ≤ ‖clunieS ζ (k + 1)‖ := norm_nonneg _
          have h_strict' : ‖clunieS ζ (k + 1)‖ < 2 * Real.sqrt ((k : ℝ) + 1) := by
            convert h_strict using 2
            push_cast; ring
          have h_sq_lt : ‖clunieS ζ (k + 1)‖ ^ 2 < (2 * Real.sqrt ((k : ℝ) + 1)) ^ 2 := by
            apply sq_lt_sq' _ h_strict'
            have h_sqrt_nn' : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
            linarith
          have h_sq_eq : (2 * Real.sqrt (k + 1)) ^ 2 = 4 * (k + 1 : ℕ) := by
            rw [mul_pow]
            have hkp1_nn : (0 : ℝ) ≤ ((k : ℝ) + 1) := by
              have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
              linarith
            push_cast
            rw [Real.sq_sqrt hkp1_nn]
            ring
          rw [h_sq_eq] at h_sq_lt
          have h_le : (4 * (k + 1 : ℕ) : ℝ) ≤ 4 * (N₀ : ℝ) := by
            have hk_le_N₀ : (k + 1 : ℕ) ≤ N₀ := by
              have : (k₂ : ℕ) ≤ N₀ := hN₀_ge
              omega
            have : (k + 1 : ℕ) ≤ (N₀ : ℕ) := hk_le_N₀
            have : ((k + 1 : ℕ) : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast this
            linarith
          have h_r_nn : 0 ≤ r ^ (2 * (k + 1)) := pow_nonneg hr_nn _
          have h_r_le_one : r ^ (2 * (k + 1)) ≤ 1 := pow_le_one₀ hr_nn hr_lt_one.le
          have h_4k_nn : (0 : ℝ) ≤ 4 * (k + 1 : ℕ) := by positivity
          calc ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1))
              ≤ (4 * (k + 1 : ℕ) : ℝ) * r ^ (2 * (k + 1)) :=
                mul_le_mul_of_nonneg_right h_sq_lt.le h_r_nn
            _ ≤ (4 * (k + 1 : ℕ) : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left h_r_le_one h_4k_nn
            _ ≤ 4 * (N₀ : ℝ) := by linarith
      _ ≤ (k₂ : ℝ) * (4 * (N₀ : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have h_card : (Finset.Ico k₁ k₂).card ≤ k₂ := by
            rw [Nat.card_Ico]; omega
          have h_card_R : ((Finset.Ico k₁ k₂).card : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast h_card
          have h_4N₀_nn : 0 ≤ 4 * (N₀ : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right h_card_R h_4N₀_nn
      _ = 4 * (k₂ : ℝ) * (N₀ : ℝ) := by ring
      _ ≤ 4 * (N₀ : ℝ) ^ 2 := by
          have h_le : (k₂ : ℝ) ≤ (N₀ : ℝ) := hN₀_ge_k₂_R
          have h_N₀_nn : 0 ≤ (N₀ : ℝ) := le_of_lt hN₀R_pos
          have h1 : 4 * (k₂ : ℝ) * (N₀ : ℝ) ≤ 4 * (N₀ : ℝ) * (N₀ : ℝ) := by
            apply mul_le_mul_of_nonneg_right
            · linarith
            · exact h_N₀_nn
          have h2 : 4 * (N₀ : ℝ) * (N₀ : ℝ) = 4 * (N₀ : ℝ) ^ 2 := by ring
          linarith
  -- Range C (k ∈ Ico k₂ N₀², v = k+1 ∈ {k₂+1, ..., N₀²}): ‖s_v‖² < 4c²·v.
  -- Bound by 4c² · ∑'_v v·(r²)^v = 4c² · r²/(1-r²)² ≤ 4c²/(1-r²)² = 64c²(k₁+5)²·N₀².
  -- Range C bound: extracted to `clunie_range_C_bound`. The result is then
  -- multiplied out using 1/(1-r²) = 4(k₁+5)·N₀ to get 64c²(k₁+5)²·N₀².
  have h_range_C : ∑ k ∈ Finset.Ico k₂ (N₀ ^ 2),
      ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
      64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2 * (N₀ : ℝ) ^ 2 := by
    have h := clunie_range_C_bound ζ k₂ (N₀ ^ 2) hc_pos hr_nn hr_lt_one hζ_outer
    -- Rewrite 4c²/(1-r²)² = 4c²·(4(k₁+5)·N₀)² = 64c²·(k₁+5)²·N₀².
    have h_eq : 4 * c ^ 2 / (1 - r ^ 2) ^ 2 = 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2 * (N₀ : ℝ) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow, h_one_sub_inv]; ring
    linarith
  -- Combine all 4 ranges using h_split: ∑ k ∈ range N₀², f k = (range k₁) + (Ico k₁ k₂) + (Ico k₂ N₀²)
  have hk₁_le_N₀_sq : k₁ ≤ N₀ ^ 2 := by
    have h1 : k₁ ≤ k₂ := hk₁_le_k₂
    have h2 : k₂ ≤ N₀ ^ 2 := le_of_lt hN₀_lt_sq
    omega
  have hk₂_le_N₀_sq : k₂ ≤ N₀ ^ 2 := le_of_lt hN₀_lt_sq
  have h_split_3 : ∀ f : ℕ → ℝ,
      ∑ k ∈ Finset.range (N₀ ^ 2), f k =
        (∑ k ∈ Finset.range k₁, f k) + (∑ k ∈ Finset.Ico k₁ k₂, f k) +
          (∑ k ∈ Finset.Ico k₂ (N₀ ^ 2), f k) := by
    intro f
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hk₁_le_N₀_sq]
    rw [show ∑ k ∈ Finset.Ico 0 k₁, f k = ∑ k ∈ Finset.range k₁, f k from by
      rw [Finset.range_eq_Ico]]
    rw [← Finset.sum_Ico_consecutive _ hk₁_le_k₂ hk₂_le_N₀_sq]
    ring
  have h_prefix_bound : ∑ k ∈ Finset.range (N₀ ^ 2),
      ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
      ((k₁ : ℝ) + 4 + 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2) * (N₀ : ℝ) ^ 2 := by
    rw [h_split_3]
    have hN₀_sq_nn : (0 : ℝ) ≤ (N₀ : ℝ) ^ 2 := sq_nonneg _
    have hsum := add_le_add (add_le_add h_range_A h_range_B) h_range_C
    linarith
  -- Total upper bound on the tsum: prefix + tail.
  have h_total_upper : ∑' k : ℕ, ‖clunieS ζ (k + 1)‖ ^ 2 * r ^ (2 * (k + 1)) ≤
      ((k₁ : ℝ) + 4 + 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2) * (N₀ : ℝ) ^ 2 +
      (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) := by
    rw [← h_split]
    exact add_le_add h_prefix_bound h_tail_bound
  -- Combine with h_lemma1' to get the contradiction inequality.
  -- N₀²/2 + 2(k₁+5)·N₀² ≤ N₀² + Σ' ≤ N₀² + ((k₁+4 + 64c²(k₁+5)²)·N₀² + tail)
  have h_combined : (N₀ : ℝ) ^ 2 / 2 + 2 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 2 ≤
      (N₀ : ℝ) ^ 2 + ((k₁ : ℝ) + 4 + 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2) * (N₀ : ℝ) ^ 2 +
        (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) :=
    h_lemma1'.trans (by linarith)
  -- Simplify: (k₁ + 11/2 - 64c²(k₁+5)²)·N₀² ≤ tail.
  have h_contradiction_ineq : ((k₁ : ℝ) + 11 / 2 - 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2) *
      (N₀ : ℝ) ^ 2 ≤
      (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) := by linarith
  -- Plug in c² = 1/(100(k₁+5)) to compute LHS = (9k₁+57.5)/25 · N₀².
  have hc_sq : c ^ 2 = 1 / (100 * ((k₁ : ℝ) + 5)) := by
    rw [hc_def, div_pow, one_pow]
    have h_sqrt_sq : Real.sqrt ((k₁ : ℝ) + 5) ^ 2 = (k₁ : ℝ) + 5 :=
      Real.sq_sqrt (by linarith [hk₁_R_nn])
    have h_denom : (10 * Real.sqrt ((k₁ : ℝ) + 5)) ^ 2 = 100 * ((k₁ : ℝ) + 5) := by
      rw [mul_pow, h_sqrt_sq]; ring
    rw [h_denom]
  -- Substitute c² to simplify h_contradiction_ineq.
  have h_64csq_k5sq : 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2 = 16 * ((k₁ : ℝ) + 5) / 25 := by
    rw [hc_sq]
    field_simp
    ring
  -- Substitute 64c²(k₁+5)² = 16(k₁+5)/25 to get the clean form.
  have h_clean_ineq :
      (9 * (k₁ : ℝ) + 57.5) / 25 * (N₀ : ℝ) ^ 2 ≤
      (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) := by
    have h_eq : (k₁ : ℝ) + 11 / 2 - 64 * c ^ 2 * ((k₁ : ℝ) + 5) ^ 2 =
        (9 * (k₁ : ℝ) + 57.5) / 25 := by rw [h_64csq_k5sq]; ring
    have h := h_contradiction_ineq
    rw [h_eq] at h
    exact h
  -- Compute RHS using 1/(1-r²) = 4(k₁+5)N₀.
  have h_rhs_eq : (N₀ : ℝ) ^ 2 * r ^ (2 * (N₀ ^ 2 + 1)) / (1 - r ^ 2) =
      4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ) ^ 3 * r ^ (2 * (N₀ ^ 2 + 1)) := by
    rw [div_eq_mul_inv, h_one_sub_inv]; ring
  -- Bound r^{2(N₀²+1)} ≤ r^{2N₀²}.
  have h_r_pow_le : r ^ (2 * (N₀ ^ 2 + 1)) ≤ r ^ (2 * N₀ ^ 2) := by
    apply pow_le_pow_of_le_one hr_nn hr_lt_one.le
    omega
  -- Final step: numerical contradiction extracted to `clunie_exp_decay_contradiction`.
  have hr_sq_full : r ^ 2 = 1 - 1 / (4 * ((k₁ : ℝ) + 5) * (N₀ : ℝ)) := by
    rw [hr_sq_eq, hr_sq_def]
  exact clunie_exp_decay_contradiction hN₀_ge_big hr_nn hr_lt_one hr_sq_full h_clean_ineq

/-
### Clunie's linear upper bound via the van der Corput sequence

The construction is the binary van der Corput sequence:
$\mathrm{vdc}(n) := \sum_{i \ge 0} \mathrm{testBit}(n, i) / 2^{i+1}$.
We use $x_j := \mathrm{vdc}(j+1)$ so that $x_j \in (0, 1)$ (excluding $\mathrm{vdc}(0) = 0$).

Key identity (block sum):
$\sum_{j=0}^{2^r - 1} e(k \cdot \mathrm{vdc}(j)) = \prod_{i=0}^{r-1} (1 + e(k / 2^{i+1}))$
proved by induction on $r$ via $e(k \cdot \mathrm{vdc}(2^r + j)) =
e(k / 2^{r+1}) \cdot e(k \cdot \mathrm{vdc}(j))$.

The product modulus $|\prod (1 + e(k/2^{i+1}))|$ is at most $2^r$, and vanishes once $r$
exceeds the dyadic order of $k$, giving $|S_{2^r}(k)| \le k$. For arbitrary $N$ a triangle
inequality on the dyadic decomposition gives $|S_N(k)| \le 2k - 1 \le 2k$, which yields a
weaker `A_k ≤ 2k`. Clunie's exact $\le k$ bound requires phase tracking across blocks
(deferred).
-/

/-- The binary van der Corput sequence, defined recursively by
$\mathrm{vdc}(0) = 0$ and $\mathrm{vdc}(2n + b) = \mathrm{vdc}(n)/2 + b/2$.
Equivalently, $\mathrm{vdc}(n) = \sum_i b_i / 2^{i+1}$ where $b_i$ are the binary digits. -/
noncomputable def vdc : ℕ → ℝ :=
  Nat.binaryRec 0 (fun b _ x => x / 2 + (if b then (1 : ℝ) / 2 else 0))

@[category API, AMS 11]
lemma vdc_zero : vdc 0 = 0 := by
  simp [vdc]

/-- The defining recursion: $\mathrm{vdc}(2n + b) = \mathrm{vdc}(n)/2 + b/2$. -/
@[category API, AMS 11]
lemma vdc_bit (b : Bool) (n : ℕ) :
    vdc (Nat.bit b n) = vdc n / 2 + (if b then (1 : ℝ) / 2 else 0) := by
  rw [vdc, Nat.binaryRec_eq]
  · rfl
  · left; simp

/-- $\mathrm{vdc}(2n) = \mathrm{vdc}(n)/2$ (the even case of `vdc_bit`). -/
@[category API, AMS 11]
lemma vdc_two_mul (n : ℕ) : vdc (2 * n) = vdc n / 2 := by
  have h := vdc_bit false n
  simp [Nat.bit] at h
  convert h using 2

/-- $\mathrm{vdc}(2n + 1) = \mathrm{vdc}(n)/2 + 1/2$ (the odd case of `vdc_bit`). -/
@[category API, AMS 11]
lemma vdc_two_mul_add_one (n : ℕ) : vdc (2 * n + 1) = vdc n / 2 + 1 / 2 := by
  have h := vdc_bit true n
  simp [Nat.bit] at h
  convert h using 2; norm_num

/-- The van der Corput sequence is non-negative: by induction on `Nat.binaryRec`. -/
@[category API, AMS 11]
lemma vdc_nonneg (n : ℕ) : 0 ≤ vdc n := by
  induction n using Nat.binaryRec with
  | zero => simp [vdc_zero]
  | bit b n ih =>
    rw [vdc_bit]
    have h1 : 0 ≤ vdc n / 2 := by linarith
    have h2 : 0 ≤ (if b then (1 : ℝ) / 2 else 0) := by split_ifs <;> linarith
    linarith

/-- The van der Corput sequence is strictly less than $1$: by induction on `Nat.binaryRec`,
$\mathrm{vdc}(n)/2 < 1/2$ and $\mathrm{vdc}(n)/2 + 1/2 < 1$. -/
@[category API, AMS 11]
lemma vdc_lt_one (n : ℕ) : vdc n < 1 := by
  induction n using Nat.binaryRec with
  | zero => simp [vdc_zero]
  | bit b n ih =>
    rw [vdc_bit]
    have h1 : vdc n / 2 < 1 / 2 := by linarith
    cases b
    · simp; linarith
    · simp; linarith

/-- For $n \ge 1$, $\mathrm{vdc}(n) > 0$: at least one bit of $n$ is set. -/
@[category API, AMS 11]
lemma vdc_pos (n : ℕ) (hn : 1 ≤ n) : 0 < vdc n := by
  induction n using Nat.binaryRec with
  | zero => omega
  | bit b n' ih =>
    rw [vdc_bit]
    cases b
    · -- bit false n' = 2 * n', need n' ≥ 1.
      have hn' : 1 ≤ n' := by
        by_contra h
        push_neg at h
        interval_cases n'
        simp [Nat.bit] at hn
      have := ih hn'
      simp; linarith
    · -- bit true n' = 2 * n' + 1, vdc(.)/2 + 1/2 ≥ 1/2 > 0.
      have h1 : 0 ≤ vdc n' := vdc_nonneg n'
      simp; linarith

/-- The shifted van der Corput sequence $j \mapsto \mathrm{vdc}(j+1)$, which avoids the
zero value and stays in $(0, 1)$ — the witness sequence for the linear upper bound. -/
noncomputable def vdcShift (j : ℕ) : ℝ := vdc (j + 1)

/-- The shifted van der Corput sequence stays in $(0, 1)$. -/
@[category API, AMS 11]
lemma vdcShift_mem_Ioo (j : ℕ) : vdcShift j ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨vdc_pos (j + 1) (by omega), vdc_lt_one (j + 1)⟩


/-- Sum over `range (2 N)` splits into even-index and odd-index parts. -/
@[category API, AMS 11]
lemma sum_range_two_mul_eq_split {α : Type*} [AddCommMonoid α]
    (N : ℕ) (f : ℕ → α) :
    ∑ j ∈ Finset.range (2 * N), f j =
      ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ (n := 2 * N), ih,
        Finset.sum_range_succ]
    abel

/-- **Partial sum recursion (general N).** For any real $\alpha$ and natural $N$,
$$\sum_{j=0}^{2N-1} e(\alpha \cdot \mathrm{vdc}(j))
  = (1 + e(\alpha/2)) \cdot \sum_{m=0}^{N-1} e((\alpha/2) \cdot \mathrm{vdc}(m)).$$
This is the recursion underlying the block sum identity (for $N = 2^r$) and an inductive
bound on $|S_N(k)|$ for general $N$. -/
@[category API, AMS 11]
lemma vdc_partial_sum_two_mul (α : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), e (α * vdc j) =
      (1 + e (α / 2)) * ∑ j ∈ Finset.range N, e ((α / 2) * vdc j) := by
  rw [sum_range_two_mul_eq_split, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [vdc_two_mul, vdc_two_mul_add_one]
  rw [show α * (vdc m / 2) = (α / 2) * vdc m from by ring,
      show α * (vdc m / 2 + 1 / 2) = (α / 2) * vdc m + α / 2 from by ring]
  have hexp : e ((α / 2) * vdc m + α / 2) = e ((α / 2) * vdc m) * e (α / 2) := by
    unfold e
    rw [show ((2 * Real.pi * ((α / 2) * vdc m + α / 2) : ℝ) * Complex.I) =
        ((2 * Real.pi * ((α / 2) * vdc m) : ℝ) * Complex.I) +
        ((2 * Real.pi * (α / 2) : ℝ) * Complex.I) from by push_cast; ring,
      Complex.exp_add]
  rw [hexp]
  ring

/-- **Half-integer cancellation.** $1 + e(t) = 0$ when $t$ is a half-integer plus integer
(equivalently, when $2t \in \mathbb{Z}$ but $t \notin \mathbb{Z}$). For $t = k/2$ with odd $k$,
this gives $1 + e(k/2) = 0$. -/
@[category API, AMS 11]
lemma e_half_odd (k : ℕ) (hk : Odd k) : (1 : ℂ) + e (k / 2) = 0 := by
  -- Need: e(k/2) = -1 for k odd.
  -- e(k/2) = e(1/2 + (k-1)/2) = e(1/2) · e((k-1)/2). For k = 2m+1: (k-1)/2 = m integer.
  -- So e(k/2) = e(1/2) · e(m) = (-1) · 1 = -1.
  obtain ⟨m, hm⟩ := hk
  subst hm
  rw [show ((2 * m + 1 : ℕ) : ℝ) / 2 = (m : ℝ) + 1 / 2 from by push_cast; ring]
  rw [show e ((m : ℝ) + 1 / 2) = e (m : ℝ) * e (1 / 2) from by
    unfold e
    rw [show ((2 * Real.pi * ((m : ℝ) + 1 / 2) : ℝ) * Complex.I) =
        ((2 * Real.pi * (m : ℝ) : ℝ) * Complex.I) +
        ((2 * Real.pi * (1 / 2) : ℝ) * Complex.I) from by push_cast; ring,
      Complex.exp_add]]
  rw [show e ((m : ℕ) : ℝ) = 1 from e_natCast m]
  rw [show e ((1 : ℝ) / 2) = -1 from by
    -- e(1/2) = exp(πi) = -1
    unfold e
    rw [show ((2 * Real.pi * (1 / 2 : ℝ) : ℝ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_pi_mul_I]]
  ring

/-- **Bound on the block product.** For $k \ge 1$,
$\bigl|\prod_{i=0}^{r-1} (1 + e(k / 2^{i+1}))\bigr| \le k$.

Proof by strong induction on $k$:
- If $k$ is odd: the factor at $i = 0$ is $1 + e(k/2) = 0$, so the product is $0$ for $r \ge 1$.
- If $k = 2k'$ even: the factor at $i = 0$ is $1 + e(k') = 2$, and the remaining product is
  $\prod_{i=1}^{r-1} (1 + e(k'/2^i)) = B_{r-1}(k')$, so the total is $2 |B_{r-1}(k')| \le 2k' = k$
  by IH on $k' < k$. -/
@[category API, AMS 11]
lemma vdc_block_norm_le (k : ℕ) (hk : 1 ≤ k) :
    ∀ r : ℕ, ‖∏ i ∈ Finset.range r, (1 + e ((k : ℝ) / 2 ^ (i + 1)))‖ ≤ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r
    -- Case on r = 0 first.
    cases r with
    | zero => simp; exact_mod_cast hk
    | succ r =>
      rcases Nat.even_or_odd k with ⟨k', hkeq⟩ | hodd
      · -- k = 2 * k' (even). Need k' ≥ 1 (since k ≥ 1 and k = 2k').
        -- hkeq : k = k' + k'. Rewrite as k = 2 k'.
        have hk2 : k = 2 * k' := by omega
        subst hk2
        have hk'_pos : 1 ≤ k' := by omega
        have hk'_lt : k' < 2 * k' := by omega
        -- Factor at i = 0: 1 + e(k') = 2. Rest: B_r(k').
        rw [Finset.prod_range_succ' _ r]
        have h0 : (1 : ℂ) + e (((2 * k' : ℕ) : ℝ) / 2 ^ (0 + 1)) = 2 := by
          have h_eq : ((2 * k' : ℕ) : ℝ) / 2 ^ (0 + 1) = ((k' : ℕ) : ℝ) := by
            push_cast; field_simp
          rw [h_eq, e_natCast]
          ring
        have hrest : ∀ i, (1 : ℂ) + e (((2 * k' : ℕ) : ℝ) / 2 ^ (i + 1 + 1)) =
            1 + e ((k' : ℝ) / 2 ^ (i + 1)) := by
          intro i
          congr 1
          congr 1
          push_cast
          field_simp
          ring
        simp_rw [hrest]
        rw [h0]
        rw [show ‖(∏ i ∈ Finset.range r, (1 + e ((k' : ℝ) / 2 ^ (i + 1)))) * 2‖ =
            2 * ‖∏ i ∈ Finset.range r, (1 + e ((k' : ℝ) / 2 ^ (i + 1)))‖ from by
          rw [norm_mul]; simp; ring]
        have := ih k' hk'_lt hk'_pos r
        push_cast
        linarith
      · -- k odd: factor at i = 0 is 0.
        rw [Finset.prod_range_succ' _ r]
        have h : (1 : ℂ) + e ((k : ℝ) / 2 ^ (0 + 1)) = 0 := by
          have h_eq : (k : ℝ) / 2 ^ (0 + 1) = (k : ℝ) / 2 := by norm_num
          rw [h_eq]
          exact e_half_odd k hodd
        rw [h, mul_zero]
        simp

/-- For odd $k$, the partial sum at any even index vanishes:
$\sum_{j=0}^{2N - 1} e(k \cdot \mathrm{vdc}(j)) = 0$. Direct from
`vdc_partial_sum_two_mul` plus `e_half_odd`. -/
@[category API, AMS 11]
lemma vdc_partial_sum_two_mul_odd (k : ℕ) (hk : Odd k) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), e ((k : ℝ) * vdc j) = 0 := by
  rw [vdc_partial_sum_two_mul ((k : ℝ)) N, e_half_odd k hk]
  ring

/-- For odd $k$, the partial sum norm is bounded by $1$ for every $N$:
$\bigl\|\sum_{j<N} e(k \cdot \mathrm{vdc}(j))\bigr\| \le 1$.

Proof: split $N$ into even ($N = 2N'$, sum $= 0$) and odd ($N = 2N' + 1$,
sum $= 0 + e(k \cdot \mathrm{vdc}(2N'))$ which has unit modulus). -/
@[category API, AMS 11]
lemma vdc_partial_sum_norm_le_one_of_odd (k : ℕ) (hk : Odd k) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, e ((k : ℝ) * vdc j)‖ ≤ 1 := by
  rcases Nat.even_or_odd N with hNeven | hNodd
  · -- N = 2N'.
    obtain ⟨N', hN'⟩ := hNeven
    have hN2 : N = 2 * N' := by omega
    rw [hN2, vdc_partial_sum_two_mul_odd k hk]
    simp
  · -- N = 2N' + 1.
    obtain ⟨N', hN'⟩ := hNodd
    rw [hN']
    rw [show 2 * N' + 1 = 2 * N' + 1 from rfl, Finset.sum_range_succ]
    rw [vdc_partial_sum_two_mul_odd k hk]
    rw [zero_add, norm_e]

/-- **Inductive bound on partial sums.** For $k \ge 1$ and any $N$,
$\bigl\|\sum_{j<N} e(k \cdot \mathrm{vdc}(j))\bigr\| \le 2k - 1$.

Proof by strong induction on $k$:
- $k$ odd: bounded by $1 \le 2k - 1$ via `vdc_partial_sum_norm_le_one_of_odd`.
- $k = 2k'$ even: use `vdc_partial_sum_two_mul` to reduce to $\sum e(k' \cdot \mathrm{vdc}(m))$
  (with factor $(1 + e(k')) = 2$), then IH on $k' < k$. The odd-$N$ tail adds at most $1$. -/
@[category API, AMS 11]
lemma vdc_partial_sum_norm_le (k : ℕ) (hk : 1 ≤ k) :
    ∀ N, ‖∑ j ∈ Finset.range N, e ((k : ℝ) * vdc j)‖ ≤ 2 * (k : ℝ) - 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N
    rcases Nat.even_or_odd k with hkeven | hkodd
    · -- k = 2k' even.
      obtain ⟨k', hk'⟩ := hkeven
      have hk2 : k = 2 * k' := by omega
      subst hk2
      have hk'_pos : 1 ≤ k' := by omega
      have hk'_lt : k' < 2 * k' := by omega
      have ih' := ih k' hk'_lt hk'_pos
      -- Case on N parity.
      rcases Nat.even_or_odd N with hNeven | hNodd
      · -- N = 2N'. ∑ = (1 + e(k')) · ∑ e(k' vdc m) = 2 · ∑ e(k' vdc m).
        obtain ⟨N', hN'⟩ := hNeven
        have hN2 : N = 2 * N' := by omega
        rw [hN2, vdc_partial_sum_two_mul ((2 * k' : ℕ) : ℝ) N']
        have h_half : ((2 * k' : ℕ) : ℝ) / 2 = (k' : ℝ) := by push_cast; ring
        rw [h_half, e_natCast k']
        rw [show (1 : ℂ) + 1 = 2 from by ring]
        rw [norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2]
        have := ih' N'
        push_cast
        linarith
      · -- N = 2N' + 1. Use even case + extra term.
        obtain ⟨N', hN'⟩ := hNodd
        rw [hN', show 2 * N' + 1 = 2 * N' + 1 from rfl, Finset.sum_range_succ]
        -- The first part is the even case.
        rw [vdc_partial_sum_two_mul ((2 * k' : ℕ) : ℝ) N']
        have h_half : ((2 * k' : ℕ) : ℝ) / 2 = (k' : ℝ) := by push_cast; ring
        rw [h_half, e_natCast k']
        rw [show (1 : ℂ) + 1 = 2 from by ring]
        -- Want: ‖2 * (∑ e(k' vdc m)) + e(2k' vdc(2N'))‖ ≤ 2(2k') - 1.
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by simp, norm_e]
        have := ih' N'
        push_cast
        linarith
    · -- k odd.
      have h := vdc_partial_sum_norm_le_one_of_odd k hkodd N
      have : (1 : ℝ) ≤ 2 * k - 1 := by
        have hk_real : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      linarith

/-- **Clunie's exact bound: |S_N(k)| ≤ k.** For $k \ge 1$ and any $N$,
$\bigl\|\sum_{j<N} e(k \cdot \mathrm{vdc}(j))\bigr\| \le k$.

The key insight (improving over the naive `≤ 2k - 1` bound) is that for $k = 2k'$ and odd
$N = 2N' + 1$, the partial sum **telescopes**:
$$S_{2N'+1}(2k') = 2 S_{N'}(k') + e(k' \cdot \mathrm{vdc}(N'))
                = 2 S_{N'}(k') + (S_{N'+1}(k') - S_{N'}(k'))
                = S_{N'+1}(k') + S_{N'}(k').$$
By IH, both terms have norm $\le k'$, so the sum has norm $\le 2k' = k$. -/
@[category API, AMS 11]
lemma vdc_partial_sum_norm_le_clunie (k : ℕ) (hk : 1 ≤ k) :
    ∀ N, ‖∑ j ∈ Finset.range N, e ((k : ℝ) * vdc j)‖ ≤ (k : ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N
    rcases Nat.even_or_odd k with hkeven | hkodd
    · -- k = 2k' even.
      obtain ⟨k', hk'⟩ := hkeven
      have hk2 : k = 2 * k' := by omega
      subst hk2
      have hk'_pos : 1 ≤ k' := by omega
      have hk'_lt : k' < 2 * k' := by omega
      have ih' := ih k' hk'_lt hk'_pos
      rcases Nat.even_or_odd N with hNeven | hNodd
      · -- N = 2N'. ‖S_{2N'}(2k')‖ = 2‖S_{N'}(k')‖ ≤ 2k' = k.
        obtain ⟨N', hN'⟩ := hNeven
        have hN2 : N = 2 * N' := by omega
        rw [hN2, vdc_partial_sum_two_mul ((2 * k' : ℕ) : ℝ) N']
        have h_half : ((2 * k' : ℕ) : ℝ) / 2 = (k' : ℝ) := by push_cast; ring
        rw [h_half, e_natCast k']
        rw [show (1 : ℂ) + 1 = 2 from by ring]
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by simp]
        have := ih' N'
        push_cast
        linarith
      · -- N = 2N' + 1. Use telescoping: S_{2N'+1}(2k') = S_{N'+1}(k') + S_{N'}(k').
        obtain ⟨N', hN'⟩ := hNodd
        rw [hN', show 2 * N' + 1 = 2 * N' + 1 from rfl, Finset.sum_range_succ]
        rw [vdc_partial_sum_two_mul ((2 * k' : ℕ) : ℝ) N']
        have h_half : ((2 * k' : ℕ) : ℝ) / 2 = (k' : ℝ) := by push_cast; ring
        rw [h_half, e_natCast k']
        rw [show (1 : ℂ) + 1 = 2 from by ring]
        rw [show vdc (2 * N') = vdc N' / 2 from vdc_two_mul N']
        rw [show ((2 * k' : ℕ) : ℝ) * (vdc N' / 2) = (k' : ℝ) * vdc N' from by push_cast; ring]
        -- Telescope: e(k' vdc N') = S_{N'+1}(k') - S_{N'}(k').
        have h_diff : e ((k' : ℝ) * vdc N') =
            (∑ j ∈ Finset.range (N' + 1), e ((k' : ℝ) * vdc j)) -
            (∑ j ∈ Finset.range N', e ((k' : ℝ) * vdc j)) := by
          rw [Finset.sum_range_succ]; ring
        rw [h_diff]
        rw [show 2 * (∑ j ∈ Finset.range N', e ((k' : ℝ) * vdc j)) +
              ((∑ j ∈ Finset.range (N' + 1), e ((k' : ℝ) * vdc j)) -
               (∑ j ∈ Finset.range N', e ((k' : ℝ) * vdc j))) =
              (∑ j ∈ Finset.range (N' + 1), e ((k' : ℝ) * vdc j)) +
              (∑ j ∈ Finset.range N', e ((k' : ℝ) * vdc j))
             from by ring]
        refine le_trans (norm_add_le _ _) ?_
        have h1 := ih' (N' + 1)
        have h2 := ih' N'
        push_cast
        linarith
    · -- k odd. |S_N(k)| ≤ 1 ≤ k.
      have h := vdc_partial_sum_norm_le_one_of_odd k hkodd N
      have hk_real : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith

/-- **Block sum identity (Clunie/van der Corput).** For any real $\alpha$ and natural $r$,
$$\sum_{j=0}^{2^r - 1} e(\alpha \cdot \mathrm{vdc}(j))
  = \prod_{i=0}^{r-1} \bigl(1 + e(\alpha / 2^{i+1})\bigr).$$
The proof is by induction on $r$, splitting the sum by parity (using
`vdc_two_mul` and `vdc_two_mul_add_one`). -/
@[category API, AMS 11]
lemma vdc_block_sum (α : ℝ) (r : ℕ) :
    ∑ j ∈ Finset.range (2 ^ r), e (α * vdc j) =
      ∏ i ∈ Finset.range r, (1 + e (α / 2 ^ (i + 1))) := by
  induction r generalizing α with
  | zero => simp [vdc_zero]
  | succ r ih =>
    -- 2^{r+1} = 2 · 2^r. Split sum by parity.
    rw [show (2 : ℕ) ^ (r + 1) = 2 * 2 ^ r from by ring,
        sum_range_two_mul_eq_split]
    -- Use vdc_two_mul and vdc_two_mul_add_one to rewrite each term.
    have h_term : ∀ m, e (α * vdc (2 * m)) + e (α * vdc (2 * m + 1)) =
        e ((α / 2) * vdc m) * (1 + e (α / 2)) := by
      intro m
      rw [vdc_two_mul, vdc_two_mul_add_one]
      have : α * (vdc m / 2) = (α / 2) * vdc m := by ring
      rw [show α * (vdc m / 2) = (α / 2) * vdc m from by ring,
          show α * (vdc m / 2 + 1 / 2) = (α / 2) * vdc m + α / 2 from by ring]
      -- e(a + b) = e(a) e(b)
      have hexp : e ((α / 2) * vdc m + α / 2) = e ((α / 2) * vdc m) * e (α / 2) := by
        unfold e
        rw [show ((2 * Real.pi * ((α / 2) * vdc m + α / 2) : ℝ) * Complex.I) =
            ((2 * Real.pi * ((α / 2) * vdc m) : ℝ) * Complex.I) +
            ((2 * Real.pi * (α / 2) : ℝ) * Complex.I) from by push_cast; ring,
          Complex.exp_add]
      rw [hexp]
      ring
    simp_rw [h_term, ← Finset.sum_mul]
    rw [ih (α / 2)]
    -- Now: ∏_{i<r} (1 + e((α/2)/2^(i+1))) * (1 + e(α/2)) = ∏_{i<r+1} (1 + e(α/2^(i+1)))
    -- Simplify (α/2) / 2^(i+1) = α / 2^(i+2).
    have hsimp : ∀ i : ℕ, α / 2 / 2 ^ (i + 1) = α / 2 ^ (i + 2) := fun i => by
      field_simp; ring
    simp_rw [hsimp]
    -- Now: ∏_{i<r} (1 + e(α/2^(i+2))) * (1 + e(α/2)) = ∏_{i<r+1} (1 + e(α/2^(i+1)))
    rw [Finset.prod_range_succ' (fun i => 1 + e (α / 2 ^ (i + 1))) r]
    -- (1 + e(α/2^(0+1))) = (1 + e(α/2)). Rest matches.
    simp [show (2 : ℝ) ^ (0 + 1) = 2 from by norm_num]

/-- **Linear upper bound (weakened).** A first weakened version of Clunie's `A_k ≤ k`: there
exists a sequence $x \in (0,1)$ with $A_k \le 2k$ for all $k \ge 1$.

The witness is the (shifted) van der Corput sequence `vdcShift`. The bound follows from the
naive triangle-inequality bound `vdc_partial_sum_norm_le` ($|S_N(k)| \le 2k - 1$) plus the
off-by-one from the shift, giving $|\sum| \le 2k$ uniformly.

For the tighter $A_k \le k + 1$ bound (using Clunie's exact phase-tracking analysis), see
`linear_upper_bound_clunie`. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.linear_upper_bound_weak :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ ((2 * k : ℝ) : EReal) := by
  refine ⟨vdcShift, vdcShift_mem_Ioo, ?_⟩
  intro k hk
  unfold A
  have hbound : ∀ n : ℕ,
      ‖∑ j ∈ Finset.range n, e ((k : ℝ) * vdcShift j)‖ ≤ 2 * (k : ℝ) := by
    intro n
    have h_eq : ∑ j ∈ Finset.range n, e ((k : ℝ) * vdcShift j) =
        (∑ j ∈ Finset.range (n + 1), e ((k : ℝ) * vdc j)) - 1 := by
      unfold vdcShift
      rw [Finset.sum_range_succ' (fun j => e ((k : ℝ) * vdc j)) n]
      rw [show (k : ℝ) * vdc 0 = 0 from by rw [vdc_zero]; ring,
          show e (0 : ℝ) = 1 from e_zero]
      ring
    rw [h_eq]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := vdc_partial_sum_norm_le k hk (n + 1)
    have h2 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h2]
    linarith
  calc atTop.limsup (fun n : ℕ => ((‖∑ j ∈ range n, e ((k : ℝ) * vdcShift j)‖ : ℝ) : EReal))
      ≤ atTop.limsup (fun _ : ℕ => (((2 * k : ℝ) : ℝ) : EReal)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => by
          show ((‖∑ j ∈ range n, e ((k : ℝ) * vdcShift j)‖ : ℝ) : EReal) ≤
            (((2 * k : ℝ) : ℝ) : EReal)
          exact_mod_cast hbound n)
    _ = (((2 * k : ℝ) : ℝ) : EReal) := Filter.limsup_const _

/-- **Linear upper bound (tight via Clunie phase tracking).** Tighter than `linear_upper_bound_weak`:
there exists a sequence $x \in (0,1)$ with $A_k \le k + 1$ for all $k \ge 1$.

The witness is the (shifted) van der Corput sequence `vdcShift`. The bound combines Clunie's
exact bound `vdc_partial_sum_norm_le_clunie` ($|S_N(k)| \le k$, proved by phase tracking via
the telescoping identity $S_{2N+1}(2k') = S_{N+1}(k') + S_N(k')$) with the off-by-one from the
shift ($\sum e(k \cdot \mathrm{vdcShift}\,j) = S_{n+1}(k) - 1$), giving $|\sum| \le k + 1$
uniformly via the triangle inequality.

This is the bound the current `vdcShift` argument yields. Whether the $+1$ can be eliminated
to recover Clunie's exact $A_k \le k$ under the strict $\mathrm{Ioo}\,0\,1$ hypothesis is open
in this formalization (see `linear_upper_bound`). -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.linear_upper_bound_clunie :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ (((k : ℝ) + 1) : EReal) := by
  refine ⟨vdcShift, vdcShift_mem_Ioo, ?_⟩
  intro k hk
  unfold A
  have hbound : ∀ n : ℕ,
      ‖∑ j ∈ Finset.range n, e ((k : ℝ) * vdcShift j)‖ ≤ (k : ℝ) + 1 := by
    intro n
    have h_eq : ∑ j ∈ Finset.range n, e ((k : ℝ) * vdcShift j) =
        (∑ j ∈ Finset.range (n + 1), e ((k : ℝ) * vdc j)) - 1 := by
      unfold vdcShift
      rw [Finset.sum_range_succ' (fun j => e ((k : ℝ) * vdc j)) n]
      rw [show (k : ℝ) * vdc 0 = 0 from by rw [vdc_zero]; ring,
          show e (0 : ℝ) = 1 from e_zero]
      ring
    rw [h_eq]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := vdc_partial_sum_norm_le_clunie k hk (n + 1)
    have h2 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h2]
    linarith
  calc atTop.limsup (fun n : ℕ => ((‖∑ j ∈ range n, e ((k : ℝ) * vdcShift j)‖ : ℝ) : EReal))
      ≤ atTop.limsup (fun _ : ℕ => (((k : ℝ) + 1 : ℝ) : EReal)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => by
          show ((‖∑ j ∈ range n, e ((k : ℝ) * vdcShift j)‖ : ℝ) : EReal) ≤
            (((k : ℝ) + 1 : ℝ) : EReal)
          exact_mod_cast hbound n)
    _ = (((k : ℝ) + 1 : ℝ) : EReal) := Filter.limsup_const _

/-- Clunie [Cl67] proved that there exists an infinite sequence $\{z_\nu\}$ on the unit circle
with $A_\nu \le \nu$ for all $\nu \ge 1$. Translating $z_\nu = e(x_\nu)$ via the standard
parameterization $\theta \mapsto e^{2\pi i \theta}$, the natural domain of $x_\nu$ is the
half-open unit interval $\mathrm{Ico}\,0\,1$, which parameterizes the unit circle bijectively.
This is the formulation we use here, matching the original [Er64b]/[Cl67] statement: any unit
complex number is allowed, including $z = 1$ (i.e., $x = 0$).

The witness is the (unshifted) van der Corput sequence `vdc` (page 4 of [Cl67] gives the
equivalent inductive doubling construction $z_{\nu + 2^k} = e^{i\pi/2^k} z_\nu$, $z_1 = 1$,
which corresponds to bit-reversal — the same as `vdc`). The bound $|S_N(k)| \le k$ is
`vdc_partial_sum_norm_le_clunie`, proved by phase tracking via the telescoping identity
$S_{2N+1}(2k') = S_{N+1}(k') + S_N(k')$.

**Note**: erdosproblems.com/987 phrases the problem with the *open* interval
$x_\nu \in (0, 1)$, which excludes the point $z = 1$ from the unit circle.
That phrasing is strictly stronger than what [Er64b]/[Cl67] state — it would force
$z_1 \ne 1$, breaking Clunie's witness at $\nu = 1$. The website-tightening appears to be
an editorial choice that misses Clunie's specific construction; we align with the original
papers here. The shifted-vdc $\le k + 1$ variant under the open interval is preserved as
`linear_upper_bound_clunie`. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.linear_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ico (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ ((k : ℝ) : EReal) := by
  refine ⟨vdc, fun j => ⟨vdc_nonneg j, vdc_lt_one j⟩, ?_⟩
  intro k hk
  unfold A
  have hbound : ∀ n : ℕ,
      ‖∑ j ∈ Finset.range n, e ((k : ℝ) * vdc j)‖ ≤ (k : ℝ) :=
    vdc_partial_sum_norm_le_clunie k hk
  calc atTop.limsup (fun n : ℕ => ((‖∑ j ∈ range n, e ((k : ℝ) * vdc j)‖ : ℝ) : EReal))
      ≤ atTop.limsup (fun _ : ℕ => (((k : ℝ) : ℝ) : EReal)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => by
          show ((‖∑ j ∈ range n, e ((k : ℝ) * vdc j)‖ : ℝ) : EReal) ≤
            (((k : ℝ) : ℝ) : EReal)
          exact_mod_cast hbound n)
    _ = (((k : ℝ) : ℝ) : EReal) := Filter.limsup_const _

/- ## [APSSV26b §3] Construction: prefix-scrambled van der Corput sequence -/

/-- The first `i` low-order binary digits of `n`, returned as a `List Bool` (LSB first).

This represents the prefix $d_0 d_1 \cdots d_{i-1}$ used to index the random bit
$\eta_{d_0 \cdots d_{i-1}}$ in [APSSV26b §3]. -/
@[category API, AMS 11]
def apssvPrefix (n : ℕ) : ℕ → List Bool
  | 0 => []
  | (i + 1) => apssvPrefix n i ++ [n.testBit i]

@[category API, AMS 11]
lemma apssvPrefix_zero (n : ℕ) : apssvPrefix n 0 = [] := rfl

@[category API, AMS 11]
lemma apssvPrefix_succ (n i : ℕ) :
    apssvPrefix n (i + 1) = apssvPrefix n i ++ [n.testBit i] := rfl

/-- The `apssvPrefix` of `n` at length `i` is a list of length `i`. -/
@[category API, AMS 11]
lemma apssvPrefix_length (n i : ℕ) : (apssvPrefix n i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [apssvPrefix_succ]; simp [ih]

/-- The randomized van der Corput sequence of [APSSV26b §3.2]. Given a "scrambling
function" `η : List Bool → Bool` (the random Bernoulli draws indexed by binary words),
$$ x_n := \sum_{i \ge 0} \frac{d_i \oplus \eta(d_0 \cdots d_{i-1})}{2^{i+1}}, $$
where $d_i$ are the binary digits of $n$ from low to high.

If `η` is identically `false`, this reduces to the standard binary van der Corput
sequence (compare `vdc` defined earlier in the file).

Implementation: the sum is an *infinite* series (geometrically dominated by
$\sum_i (1/2)^{i+1} = 1$, so summable). For `η ≡ false` this collapses to a finite
sum (only the finitely many nonzero digits of `n` contribute), recovering the
standard binary van der Corput sequence. For general `η`, the bits beyond the
highest digit of `n` are zero but their XOR with `η` need not be — these contribute
the random "tail piece" $T_{w,P}$ that drives the block-sum identity in
Proposition 3.4 of [APSSV26b].

**Possible refactor**: This series is an instance of `Real.ofDigits` (Mathlib's
base-`b` digit-expansion API in `Mathlib/Analysis/Real/OfDigits.lean`) at base 2,
with digit $d_i \oplus \eta(\text{prefix}_i) : \mathrm{Fin}\,2$. Using `Real.ofDigits`
would let `apssvX_summable`, `apssvX_nonneg`, `apssvX_le_one` come for free from
`Real.summable_ofDigitsTerm`, `Real.ofDigits_nonneg`, `Real.ofDigits_le_one`, and
measurability from `Real.continuous_ofDigits`. We keep the explicit form here
because the block-sum identity (Proposition 3.4) is most natural with explicit
testBit/prefix manipulation. -/
@[category API, AMS 11]
noncomputable def apssvX (η : List Bool → Bool) (n : ℕ) : ℝ :=
  ∑' i : ℕ, (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)

/-- Each summand in `apssvX` is in `[0, (1/2)^{i+1}]`. -/
@[category API, AMS 11]
lemma apssvX_summand_le (η : List Bool → Bool) (n i : ℕ) :
    (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1) ≤
      (1 / 2) ^ (i + 1) := by
  have h_pow_eq : (1 / 2 : ℝ) ^ (i + 1) = 1 / 2 ^ (i + 1) := by
    rw [div_pow, one_pow]
  have h_pow_pos : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  rw [h_pow_eq]
  split_ifs
  · exact le_refl _
  · exact div_le_div_of_nonneg_right zero_le_one h_pow_pos.le

@[category API, AMS 11]
lemma apssvX_summand_nonneg (η : List Bool → Bool) (n i : ℕ) :
    0 ≤ (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1) := by
  have h_pow_pos : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  split_ifs with h
  · exact div_nonneg zero_le_one h_pow_pos.le
  · exact div_nonneg le_rfl h_pow_pos.le

/-- Summability of the `apssvX` series, by comparison with the geometric series. -/
@[category API, AMS 11]
lemma apssvX_summable (η : List Bool → Bool) (n : ℕ) :
    Summable (fun i : ℕ =>
      (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)) := by
  apply Summable.of_nonneg_of_le (apssvX_summand_nonneg η n) (apssvX_summand_le η n)
  have h_geom := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact h_geom.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)

/-- `apssvX η n ≥ 0`. -/
@[category API, AMS 11]
lemma apssvX_nonneg (η : List Bool → Bool) (n : ℕ) : 0 ≤ apssvX η n :=
  tsum_nonneg (apssvX_summand_nonneg η n)

/-- `apssvX η n ≤ 1`, by termwise comparison with $\sum_{i \ge 0} (1/2)^{i+1} = 1$. -/
@[category API, AMS 11]
lemma apssvX_le_one (η : List Bool → Bool) (n : ℕ) : apssvX η n ≤ 1 := by
  have h_summable_geom : Summable (fun i : ℕ => ((1 / 2 : ℝ)) ^ (i + 1)) := by
    have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact h.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  calc apssvX η n
      ≤ ∑' i : ℕ, ((1 / 2 : ℝ)) ^ (i + 1) :=
        Summable.tsum_le_tsum (apssvX_summand_le η n) (apssvX_summable η n) h_summable_geom
    _ = (1 / 2) * ∑' i : ℕ, ((1 / 2 : ℝ)) ^ i := by
        rw [← tsum_mul_left]; congr 1; funext i; rw [pow_succ]; ring
    _ = (1 / 2) * (1 - (1 / 2 : ℝ))⁻¹ := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 1 := by norm_num

/-- The first `i` bits of a word `w : Fin r → Bool` (with `i ≤ r`), packaged as a `List Bool`. -/
@[category API, AMS 11]
def apssvWordPrefix {r : ℕ} (w : Fin r → Bool) : ℕ → List Bool
  | 0 => []
  | (i + 1) => apssvWordPrefix w i ++
      [if h : i < r then w ⟨i, h⟩ else false]

/-- The scrambled prefix integer of [APSSV26b (3.2)]:
$$ j_r(w) := \sum_{i = 0}^{r-1} \big(w_i \oplus \eta_{w_0 \cdots w_{i-1}}\big) \cdot 2^{r-1-i}, $$
read with $w_0$ as the most significant bit of $j_r(w)$. Here we represent $w \in \{0,1\}^r$
as a function `Fin r → Bool`.

This is an `ℕ`-valued helper; one further shows `apssvJ η r w < 2^r`. -/
@[category API, AMS 11]
def apssvJ (η : List Bool → Bool) (r : ℕ) (w : Fin r → Bool) : ℕ :=
  (Finset.range r).sum fun i =>
    if h : i < r then
      if (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) then 2 ^ (r - 1 - i) else 0
    else 0

/-- `apssvJ η r w < 2^r`: each digit-bit contributes at most $2^{r-1-i}$, and
$\sum_{i=0}^{r-1} 2^{r-1-i} = 2^r - 1 < 2^r$. -/
@[category API, AMS 11]
private lemma apssv_geom_sum (r : ℕ) :
    (∑ i ∈ Finset.range r, 2 ^ (r - 1 - i)) = 2 ^ r - 1 := by
  rw [Finset.sum_range_reflect (fun i => 2 ^ i) r]
  induction r with
  | zero => simp
  | succ r' ih =>
    rw [Finset.sum_range_succ, ih]
    have : 2 ^ (r' + 1) = 2 * 2 ^ r' := by rw [pow_succ]; ring
    omega

@[category API, AMS 11]
lemma apssvJ_lt_two_pow (η : List Bool → Bool) (r : ℕ) (w : Fin r → Bool) :
    apssvJ η r w < 2 ^ r := by
  have h_bd : apssvJ η r w ≤ ∑ i ∈ Finset.range r, 2 ^ (r - 1 - i) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp
  have h_sum_eq := apssv_geom_sum r
  have h_pow_pos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  omega

/-- Cardinality fact: $|\mathrm{Fin}\,r \to \mathrm{Bool}| = 2^r$, matching $|\mathrm{Fin}\,(2^r)|$. -/
@[category API, AMS 11]
lemma apssv_card_word_eq_two_pow (r : ℕ) :
    Fintype.card (Fin r → Bool) = 2 ^ r := by
  simp

/-- The "topbit" of `apssvJ η (r+1) w`: dividing by $2^r$ gives exactly
$w_0 \oplus \eta_\emptyset \in \{0,1\}$.

This isolates the contribution of position $r$ (the MSB of the $(r+1)$-bit output)
from the lower-order contributions, which together are bounded by $2^r - 1 < 2^r$. -/
@[category API, AMS 11]
lemma apssvJ_topBit (η : List Bool → Bool) (r : ℕ) (w : Fin (r + 1) → Bool) :
    apssvJ η (r + 1) w / 2 ^ r =
      (if (w 0).xor (η []) then 1 else 0) := by
  -- Define f := i ↦ (term in the apssvJ sum).
  set f : ℕ → ℕ := fun i => if h : i < r + 1 then
    if (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) then 2 ^ (r + 1 - 1 - i) else 0
  else 0 with hf_def
  -- Split off i = 0.
  have h_zero_mem : (0 : ℕ) ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  show (∑ i ∈ Finset.range (r + 1), f i) / 2 ^ r =
    if (w 0).xor (η []) then 1 else 0
  rw [← Finset.add_sum_erase _ f h_zero_mem]
  -- Compute f 0.
  have h_zero_term : f 0 = if (w 0).xor (η []) then 2 ^ r else 0 := by
    show (if h : 0 < r + 1 then
        if (w ⟨0, h⟩).xor (η (apssvWordPrefix w 0)) then 2 ^ (r + 1 - 1 - 0) else 0
      else 0) = _
    rw [dif_pos (Nat.zero_lt_succ r)]
    show (if (w ⟨(0 : ℕ), _⟩).xor (η (apssvWordPrefix w (0 : ℕ))) then _ else _) = _
    have h1 : (⟨(0 : ℕ), Nat.zero_lt_succ r⟩ : Fin (r + 1)) = 0 := rfl
    have h2 : apssvWordPrefix w (0 : ℕ) = [] := rfl
    rw [h1, h2]
    simp
  rw [h_zero_term]
  -- Bound the "rest" sum by 2^r - 1 < 2^r.
  have h_le : ∀ i ∈ (Finset.range (r + 1)).erase 0, f i ≤ 2 ^ (r - i) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    obtain ⟨hi_ne, hi_lt⟩ := hi
    show (if h : i < r + 1 then
        if (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) then 2 ^ (r + 1 - 1 - i) else 0
      else 0) ≤ 2 ^ (r - i)
    rw [dif_pos hi_lt]
    have h_eq : r + 1 - 1 - i = r - i := by omega
    rw [h_eq]
    split_ifs <;> simp
  have h_geom_eq :
      ∑ i ∈ (Finset.range (r + 1)).erase 0, 2 ^ (r - i) = 2 ^ r - 1 := by
    have h_setEq : (Finset.range (r + 1)).erase 0 = (Finset.range r).image (· + 1) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx_ne, hx_lt⟩
        refine ⟨x - 1, ?_, ?_⟩ <;> omega
      · rintro ⟨y, hy_lt, rfl⟩; exact ⟨by omega, by omega⟩
    rw [h_setEq]
    have h_inj : Set.InjOn (fun x : ℕ => x + 1) (Finset.range r : Set ℕ) := fun a _ b _ h => by
      simp at h; exact h
    rw [Finset.sum_image (fun a _ b _ h => Nat.succ_injective h)]
    have h_step : ∀ y ∈ Finset.range r, (2 : ℕ) ^ (r - (y + 1)) = 2 ^ (r - 1 - y) := by
      intros y hy
      rw [Finset.mem_range] at hy
      congr 1; omega
    rw [Finset.sum_congr rfl h_step]
    exact apssv_geom_sum r
  have h_rest_lt : (∑ i ∈ (Finset.range (r + 1)).erase 0, f i) < 2 ^ r := by
    calc (∑ i ∈ (Finset.range (r + 1)).erase 0, f i)
        ≤ ∑ i ∈ (Finset.range (r + 1)).erase 0, 2 ^ (r - i) := Finset.sum_le_sum h_le
      _ = 2 ^ r - 1 := h_geom_eq
      _ < 2 ^ r := by have := Nat.one_le_two_pow (n := r); omega
  -- Combine: (top + rest) / 2^r where top ∈ {0, 2^r} and rest < 2^r.
  split_ifs with h_xor
  · -- (2^r + rest) / 2^r = 1.
    have h_pow_pos : 0 < 2 ^ r := Nat.two_pow_pos r
    rw [show (2 ^ r + (∑ i ∈ (Finset.range (r + 1)).erase 0, f i)) / 2 ^ r =
        ((∑ i ∈ (Finset.range (r + 1)).erase 0, f i) + 1 * 2 ^ r) / 2 ^ r by ring_nf]
    rw [Nat.add_mul_div_right _ _ h_pow_pos]
    rw [Nat.div_eq_of_lt h_rest_lt]
  · rw [zero_add]
    exact Nat.div_eq_of_lt h_rest_lt

/-- Index-shift identity for `apssvWordPrefix`: the prefix of `w : Fin (r+1) → Bool`
at position `j+1` is the cons `w 0 :: (prefix of (Fin.succ-shifted w) at position j)`. -/
@[category API, AMS 11]
lemma apssvWordPrefix_shift {r : ℕ} (w : Fin (r + 1) → Bool) (j : ℕ) :
    j ≤ r →
      apssvWordPrefix w (j + 1) =
        w 0 :: apssvWordPrefix (fun i : Fin r => w i.succ) j := by
  induction j with
  | zero =>
    intro _
    show apssvWordPrefix w 0 ++ [if h : (0 : ℕ) < r + 1 then w ⟨0, h⟩ else false] =
        w 0 :: apssvWordPrefix (fun i : Fin r => w i.succ) 0
    simp only [apssvWordPrefix, Nat.zero_lt_succ, dif_pos]
    rfl
  | succ j ih =>
    intro hj
    have hj' : j ≤ r := by omega
    have ih' := ih hj'
    show apssvWordPrefix w (j + 1) ++
        [if h : j + 1 < r + 1 then w ⟨j + 1, h⟩ else false] =
        w 0 :: (apssvWordPrefix (fun i : Fin r => w i.succ) j ++
          [if h : j < r then (fun i : Fin r => w i.succ) ⟨j, h⟩ else false])
    have hj_lt₁ : j + 1 < r + 1 := by omega
    have hj_lt₂ : j < r := by omega
    rw [dif_pos hj_lt₁, dif_pos hj_lt₂]
    have h_cast : w ⟨j + 1, hj_lt₁⟩ = w (⟨j, hj_lt₂⟩ : Fin r).succ := rfl
    rw [h_cast, ih']
    rfl

/-- Decomposition of `apssvJ η (r+1) w` into the top-bit contribution plus the
"lower" `apssvJ` over a shifted word with shifted η.

If `tailW i := w i.succ` and `tailEta u := η (w 0 :: u)`, then
$$ \mathrm{apssvJ}\,\eta\,(r+1)\,w =
   (\mathrm{topbit}) + \mathrm{apssvJ}\,\mathrm{tailEta}\,r\,\mathrm{tailW}, $$
where $\mathrm{topbit} = w_0 \oplus \eta_\emptyset$ contributes either $2^r$ or $0$. -/
@[category API, AMS 11]
lemma apssvJ_decompose (η : List Bool → Bool) (r : ℕ) (w : Fin (r + 1) → Bool) :
    apssvJ η (r + 1) w =
      (if (w 0).xor (η []) then 2 ^ r else 0) +
      apssvJ (fun u => η (w 0 :: u)) r (fun i : Fin r => w i.succ) := by
  unfold apssvJ
  -- Define the term function f for the (r+1)-sum.
  set f : ℕ → ℕ := fun i => if h : i < r + 1 then
    if (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) then 2 ^ (r + 1 - 1 - i) else 0
  else 0 with hf_def
  -- Set the term function g for the r-sum (over shifted word and shifted η).
  set tailW : Fin r → Bool := fun i => w i.succ with hTailW
  set tailEta : List Bool → Bool := fun u => η (w 0 :: u) with hTailEta
  set g : ℕ → ℕ := fun j => if h : j < r then
    if (tailW ⟨j, h⟩).xor (tailEta (apssvWordPrefix tailW j)) then 2 ^ (r - 1 - j) else 0
  else 0 with hg_def
  -- Split off i = 0.
  have h_zero_mem : (0 : ℕ) ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  show (∑ i ∈ Finset.range (r + 1), f i) = _ + ∑ j ∈ Finset.range r, g j
  rw [← Finset.add_sum_erase _ f h_zero_mem]
  -- Compute f 0 = top-bit contribution.
  have h_zero_term : f 0 = if (w 0).xor (η []) then 2 ^ r else 0 := by
    show (if h : 0 < r + 1 then
        if (w ⟨0, h⟩).xor (η (apssvWordPrefix w 0)) then 2 ^ (r + 1 - 1 - 0) else 0
      else 0) = _
    rw [dif_pos (Nat.zero_lt_succ r)]
    have h1 : (⟨(0 : ℕ), Nat.zero_lt_succ r⟩ : Fin (r + 1)) = 0 := rfl
    have h2 : apssvWordPrefix w (0 : ℕ) = [] := rfl
    rw [h1, h2]
    simp
  rw [h_zero_term]
  -- Reindex erase to image.
  have h_setEq : (Finset.range (r + 1)).erase 0 = (Finset.range r).image (· + 1) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx_ne, hx_lt⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy_lt, rfl⟩; exact ⟨by omega, by omega⟩
  rw [h_setEq, Finset.sum_image (fun a _ b _ h => Nat.succ_injective h)]
  -- Show: f (j+1) = g j for j ∈ range r.
  apply congr_arg₂ _ rfl
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  -- f (j+1) = if (j+1) < r+1 then ... else 0; the cond holds.
  have hj_lt : j + 1 < r + 1 := by omega
  show (if h : j + 1 < r + 1 then
      if (w ⟨j + 1, h⟩).xor (η (apssvWordPrefix w (j + 1))) then 2 ^ (r + 1 - 1 - (j + 1)) else 0
    else 0) =
    (if h : j < r then
      if (tailW ⟨j, h⟩).xor (tailEta (apssvWordPrefix tailW j)) then 2 ^ (r - 1 - j) else 0
    else 0)
  rw [dif_pos hj_lt, dif_pos hj]
  -- Match the bit conditions and the powers.
  have h_pow_eq : (r + 1 - 1 - (j + 1)) = (r - 1 - j) := by omega
  rw [h_pow_eq]
  -- The Fin index w ⟨j+1, hj_lt⟩ = w (Fin.succ ⟨j, hj⟩) = tailW ⟨j, hj⟩.
  have h_fin_eq : (⟨j + 1, hj_lt⟩ : Fin (r + 1)) = (⟨j, hj⟩ : Fin r).succ := by
    apply Fin.ext; rfl
  rw [h_fin_eq]
  show (if (w (⟨j, hj⟩ : Fin r).succ).xor (η (apssvWordPrefix w (j + 1))) then _ else _) =
      if (tailW ⟨j, hj⟩).xor (tailEta (apssvWordPrefix tailW j)) then _ else _
  -- tailW ⟨j, hj⟩ = w (Fin.succ ⟨j, hj⟩) by definition.
  show (if (w (⟨j, hj⟩ : Fin r).succ).xor (η (apssvWordPrefix w (j + 1))) then _ else _) =
      if (w (⟨j, hj⟩ : Fin r).succ).xor (tailEta (apssvWordPrefix tailW j)) then _ else _
  -- The remaining match: η (apssvWordPrefix w (j+1)) = tailEta (apssvWordPrefix tailW j).
  rw [apssvWordPrefix_shift w j (by omega)]

/-- Injectivity of `apssvJ`: if two words give the same output, they must agree.

**Proof by induction on r.**
- For r = 0: both words are functions `Fin 0 → Bool`, so trivially equal.
- For r+1: by `apssvJ_topBit`, the high bit determines $w_0$, so $w_0$ matches.
  Then by `apssvJ_decompose`, the rest is `apssvJ` over a shifted word with shifted η;
  apply IH with the shifted η. -/
@[category API, AMS 11]
lemma apssvJ_injective : ∀ (η : List Bool → Bool) (r : ℕ),
    Function.Injective (apssvJ η r) := by
  intro η r
  induction r generalizing η with
  | zero =>
    intro w₁ w₂ _
    funext i
    exact i.elim0
  | succ r ih =>
    intro w₁ w₂ heq
    -- Step 1: w₁ 0 = w₂ 0 from topBit.
    have h_top₁ := apssvJ_topBit η r w₁
    have h_top₂ := apssvJ_topBit η r w₂
    have h_top : (if (w₁ 0).xor (η []) then 1 else 0) =
        (if (w₂ 0).xor (η []) then (1 : ℕ) else 0) := by
      rw [← h_top₁, ← h_top₂, heq]
    have h_w0 : w₁ 0 = w₂ 0 := by
      by_contra h_ne
      -- The two if-branches differ; deduce contradiction.
      cases h₁ : w₁ 0 <;> cases h₂ : w₂ 0 <;> cases h_e : η [] <;>
        simp [h₁, h₂, h_e] at h_top h_ne
    -- Step 2: shifted apssvJ values are equal, apply IH.
    have h_decomp₁ := apssvJ_decompose η r w₁
    have h_decomp₂ := apssvJ_decompose η r w₂
    have h_low : apssvJ (fun u => η (w₁ 0 :: u)) r (fun i : Fin r => w₁ i.succ) =
        apssvJ (fun u => η (w₂ 0 :: u)) r (fun i : Fin r => w₂ i.succ) := by
      have h_top_eq : (if (w₁ 0).xor (η []) then (2 : ℕ) ^ r else 0) =
          (if (w₂ 0).xor (η []) then (2 : ℕ) ^ r else 0) := by rw [h_w0]
      omega
    -- Apply IH with shifted η.
    have h_eta_eq : (fun u => η (w₁ 0 :: u)) = (fun u => η (w₂ 0 :: u)) := by
      funext u; rw [h_w0]
    rw [h_eta_eq] at h_low
    have h_tail_eq : (fun i : Fin r => w₁ i.succ) = (fun i : Fin r => w₂ i.succ) :=
      ih _ h_low
    -- Combine h_w0 (case i = 0) and h_tail_eq (cases i ≥ 1) to conclude w₁ = w₂.
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact h_w0
    · exact congr_fun h_tail_eq j

/-- Lemma 3.3 of [APSSV26b]: the map $w \mapsto j_r(w)$ is a bijection from $\{0,1\}^r$
onto $\{0, 1, \ldots, 2^r - 1\}$.

**Proof outline.** By the cardinality match between $\mathrm{Fin}\,r \to \mathrm{Bool}$ and
$\mathrm{Fin}\,(2^r)$ (both have size $2^r$), it suffices to prove injectivity. The key
observation is that the bit of $j_r(w)$ at position $r-1-i$ is exactly
$w_i \oplus \eta_{w_0 \cdots w_{i-1}}$ — since the summands at distinct positions
$2^{r-1-i}$ for $i \in \{0,\ldots,r-1\}$ are disjoint powers of $2$. Knowing the output
bits, one reconstructs $w_0$ from bit $r-1$ and $\eta_\emptyset$, then $w_1$ from bit $r-2$
and $\eta_{w_0}$, etc. Hence $w$ is uniquely determined by $j_r(w)$. -/
@[category API, AMS 11]
lemma apssvJ_bijective (η : List Bool → Bool) (r : ℕ) :
    Function.Bijective (fun w : Fin r → Bool =>
      (⟨apssvJ η r w, apssvJ_lt_two_pow η r w⟩ : Fin (2 ^ r))) := by
  -- Reduce bijectivity to injectivity via |Fin r → Bool| = 2^r = |Fin (2^r)|.
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · -- Injectivity follows from `apssvJ_injective` (the underlying ℕ-valued map is injective).
    intro w₁ w₂ h
    have : apssvJ η r w₁ = apssvJ η r w₂ := congr_arg Fin.val h
    exact apssvJ_injective η r this
  · simp

/-- The scrambled tail of [APSSV26b (3.3)] for prefix word `w : Fin r → Bool` and integer `P`:
$$ T_{w, P} := \sum_{\ell \ge 0} \frac{p_\ell \oplus \eta(w \cdot p_0 \cdots p_{\ell-1})}{2^{\ell+1}}, $$
where $p_\ell$ are the binary digits of $P$ and $w \cdot u$ denotes the concatenation of the
list-of-`w` with `u`. -/
@[category API, AMS 11]
noncomputable def apssvT (η : List Bool → Bool) {r : ℕ} (w : Fin r → Bool) (P : ℕ) : ℝ :=
  ∑' ℓ : ℕ, (if (P.testBit ℓ).xor
      (η (apssvWordPrefix w r ++ apssvPrefix P ℓ)) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1)

/-- The length of `apssvWordPrefix w n` is `n`. (For `n > r` the recursion pads
with `false` placeholders, but the length identity holds unconditionally.) -/
@[category API, AMS 11]
lemma apssvWordPrefix_length {r : ℕ} (w : Fin r → Bool) (n : ℕ) :
    (apssvWordPrefix w n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => unfold apssvWordPrefix; rw [List.length_append, ih]; simp

/-- The `i`-th element of `apssvWordPrefix w n` (for `i < n` and `i < r`) is
`w ⟨i, _⟩`. Together with `apssvWordPrefix_length`, this characterises the list
as the canonical packing of `w`. -/
@[category API, AMS 11]
lemma apssvWordPrefix_get_eq {r : ℕ} (w : Fin r → Bool) (n i : ℕ)
    (hi : i < n) (hir : i < r) :
    (apssvWordPrefix w n)[i]'(by rw [apssvWordPrefix_length]; exact hi) = w ⟨i, hir⟩ := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge i n with h_lt | h_ge
    · -- i < n: the index falls in the prefix part.
      have h_prefix_len : (apssvWordPrefix w n).length = n := apssvWordPrefix_length w n
      show (apssvWordPrefix w n ++
          [if h : n < r then w ⟨n, h⟩ else false])[i]'_ = w ⟨i, hir⟩
      rw [List.getElem_append_left (by rw [h_prefix_len]; exact h_lt)]
      exact ih h_lt
    · -- i = n (since i < n+1 and i ≥ n).
      have hi_eq : i = n := by omega
      subst hi_eq
      have h_prefix_len : (apssvWordPrefix w i).length = i := apssvWordPrefix_length w i
      show (apssvWordPrefix w i ++
          [if h : i < r then w ⟨i, h⟩ else false])[i]'_ = w ⟨i, hir⟩
      rw [List.getElem_append_right (by rw [h_prefix_len])]
      simp [hir, h_prefix_len]

/-- The map `apssvWordPrefix · r : (Fin r → Bool) → List Bool` is injective: the
list packs each bit of `w` into a definite position, so distinct `w` give distinct
prefixes. -/
@[category API, AMS 11]
lemma apssvWordPrefix_injective {r : ℕ} :
    Function.Injective (fun w : Fin r → Bool => apssvWordPrefix w r) := by
  intro w w' h
  ext ⟨i, hir⟩
  have h_get : (apssvWordPrefix w r)[i]'(by rw [apssvWordPrefix_length]; exact hir) =
      (apssvWordPrefix w' r)[i]'(by rw [apssvWordPrefix_length]; exact hir) := by
    congr 1
  rw [apssvWordPrefix_get_eq w r i hir hir, apssvWordPrefix_get_eq w' r i hir hir] at h_get
  exact h_get

/-- **Disjointness of long-prefix coordinate sets across distinct words**: for
`w ≠ w' : Fin r → Bool`, the long-prefix lists used by `apssvT η w P` and
`apssvT η w' P` are pairwise unequal:
$$ \text{apssvWordPrefix}\,w\,r \mathbin{+\!\!+} \text{apssvPrefix}\,P\,\ell \;\ne\;
   \text{apssvWordPrefix}\,w'\,r \mathbin{+\!\!+} \text{apssvPrefix}\,P\,\ell'. $$

(Combined with `apssvT_eq_of_agree`, this implies that under `apssvEtaMeasure`
the random variables `apssvT η w P` and `apssvT η w' P` are independent.) -/
@[category API, AMS 11]
lemma apssvWordPrefix_disjoint_of_ne {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w')
    (P : ℕ) (ℓ ℓ' : ℕ) :
    apssvWordPrefix w r ++ apssvPrefix P ℓ ≠
      apssvWordPrefix w' r ++ apssvPrefix P ℓ' := by
  intro h
  -- Length comparison forces ℓ = ℓ'.
  have h_len : (apssvWordPrefix w r ++ apssvPrefix P ℓ).length =
      (apssvWordPrefix w' r ++ apssvPrefix P ℓ').length := congr_arg _ h
  rw [List.length_append, List.length_append, apssvWordPrefix_length,
      apssvWordPrefix_length, apssvPrefix_length, apssvPrefix_length] at h_len
  have h_ℓ : ℓ = ℓ' := by omega
  subst h_ℓ
  -- Take the first r elements: they must agree, hence apssvWordPrefix w r = apssvWordPrefix w' r.
  have h_take : (apssvWordPrefix w r ++ apssvPrefix P ℓ).take r =
      (apssvWordPrefix w' r ++ apssvPrefix P ℓ).take r := by rw [h]
  rw [List.take_left' (apssvWordPrefix_length w r), List.take_left' (apssvWordPrefix_length w' r)]
    at h_take
  -- apssvWordPrefix is injective.
  exact hww' (apssvWordPrefix_injective h_take)

/-- **Coordinate dependence of `apssvT`**: `apssvT η w P` depends on `η` only
through the coordinates `apssvWordPrefix w r ++ apssvPrefix P ℓ` for `ℓ : ℕ`.
Concretely, if `η₁` and `η₂` agree on each such coordinate, then
`apssvT η₁ w P = apssvT η₂ w P`.

This is the prerequisite for the conditional-independence argument: for `w ≠ w'`,
`apssvWordPrefix w r ≠ apssvWordPrefix w' r` (different first-r-bit patterns of
the same length `r`), so `apssvT η w P` and `apssvT η w' P` depend on disjoint
sets of η-coordinates, hence are independent under `apssvEtaMeasure`. -/
@[category API, AMS 11]
lemma apssvT_eq_of_agree {r : ℕ} (w : Fin r → Bool) (P : ℕ) (η₁ η₂ : List Bool → Bool)
    (h : ∀ ℓ : ℕ, η₁ (apssvWordPrefix w r ++ apssvPrefix P ℓ) =
                  η₂ (apssvWordPrefix w r ++ apssvPrefix P ℓ)) :
    apssvT η₁ w P = apssvT η₂ w P := by
  unfold apssvT
  refine tsum_congr fun ℓ => ?_
  rw [h ℓ]

/-- The "factored" form of `apssvT`: a function of a Boolean sequence `b : ℕ → Bool`
(which will be plugged in as `b ℓ = η (apssvWordPrefix w r ++ apssvPrefix P ℓ)`).

This makes the coordinate dependence explicit: `apssvT η w P` is the value at
`b = η ∘ (apssvWordPrefix w r ++ apssvPrefix P ·)` of a fixed deterministic
function of `b`. -/
@[category API, AMS 11]
noncomputable def apssvT_factored (P : ℕ) (b : ℕ → Bool) : ℝ :=
  ∑' ℓ : ℕ, (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1)

/-- Factorization identity: `apssvT η w P` equals `apssvT_factored P` applied to
the projection `ℓ ↦ η (apssvWordPrefix w r ++ apssvPrefix P ℓ)`. The left-hand
side is a function of η; the projection is the only η-dependence; the rest is
a deterministic function of the bit-sequence. -/
@[category API, AMS 11]
lemma apssvT_eq_factored (η : List Bool → Bool) {r : ℕ} (w : Fin r → Bool) (P : ℕ) :
    apssvT η w P =
      apssvT_factored P (fun ℓ => η (apssvWordPrefix w r ++ apssvPrefix P ℓ)) :=
  rfl

/-- `apssvX η P = apssvT_factored P (η ∘ apssvPrefix P)`. Both random sums share
the same shape `∑' ℓ, (if testBit_P_ℓ ⊕ b_ℓ then 1 else 0) / 2^(ℓ+1)`; in
`apssvX` we plug `b_ℓ = η (apssvPrefix P ℓ)`, in `apssvT η w P` we plug
`b_ℓ = η (apssvWordPrefix w r ++ apssvPrefix P ℓ)`. -/
@[category API, AMS 11]
lemma apssvX_eq_apssvT_factored (η : List Bool → Bool) (P : ℕ) :
    apssvX η P = apssvT_factored P (fun ℓ => η (apssvPrefix P ℓ)) :=
  rfl

/-- Each summand in `apssvT_factored P` is in `[0, (1/2)^(ℓ+1)]`. -/
@[category API, AMS 11]
lemma apssvT_factored_summand_le (P : ℕ) (b : ℕ → Bool) (ℓ : ℕ) :
    (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1) ≤ (1 / 2) ^ (ℓ + 1) := by
  rw [div_pow, one_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

/-- Each summand in `apssvT_factored P` is nonneg. -/
@[category API, AMS 11]
lemma apssvT_factored_summand_nonneg (P : ℕ) (b : ℕ → Bool) (ℓ : ℕ) :
    0 ≤ (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1) := by
  apply div_nonneg _ (by positivity)
  split_ifs <;> norm_num

/-- `apssvT_factored P b` is summable for any bit-sequence `b`. -/
@[category API, AMS 11]
lemma apssvT_factored_summable (P : ℕ) (b : ℕ → Bool) :
    Summable (fun ℓ : ℕ =>
      (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1)) := by
  have h_geom_summable : Summable (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1)) := by
    have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact h.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  exact Summable.of_nonneg_of_le (apssvT_factored_summand_nonneg P b)
    (apssvT_factored_summand_le P b) h_geom_summable

/-- `apssvT_factored P b ≥ 0` for any bit-sequence `b`. -/
@[category API, AMS 11]
lemma apssvT_factored_nonneg (P : ℕ) (b : ℕ → Bool) : 0 ≤ apssvT_factored P b :=
  tsum_nonneg (apssvT_factored_summand_nonneg P b)

/-- `apssvT_factored P b ≤ 1`, by termwise comparison with $\sum_{\ell \ge 0} (1/2)^{\ell+1} = 1$. -/
@[category API, AMS 11]
lemma apssvT_factored_le_one (P : ℕ) (b : ℕ → Bool) : apssvT_factored P b ≤ 1 := by
  have h_geom_summable : Summable (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1)) := by
    have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact h.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  calc apssvT_factored P b
      ≤ ∑' ℓ : ℕ, ((1 / 2 : ℝ)) ^ (ℓ + 1) :=
        Summable.tsum_le_tsum (apssvT_factored_summand_le P b)
          (apssvT_factored_summable P b) h_geom_summable
    _ = (1 / 2) * ∑' ℓ : ℕ, ((1 / 2 : ℝ)) ^ ℓ := by
        rw [← tsum_mul_left]; congr 1; funext ℓ; rw [pow_succ]; ring
    _ = (1 / 2) * (1 - (1 / 2 : ℝ))⁻¹ := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 1 := by norm_num

/-- `apssvT_factored P` is measurable in its bit-sequence argument
`b : ℕ → Bool`. Lifted via `ENNReal.ofReal` analogously to `apssvX_measurable`. -/
@[category API, AMS 11]
lemma apssvT_factored_measurable (P : ℕ) :
    Measurable (apssvT_factored P) := by
  -- Each summand is measurable in b.
  have h_summand_meas : ∀ ℓ : ℕ, Measurable (fun b : ℕ → Bool =>
      (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1)) := by
    intro ℓ
    apply Measurable.div_const
    have : Measurable (fun bℓ : Bool =>
        if (P.testBit ℓ).xor bℓ then (1 : ℝ) else 0) := Measurable.of_discrete
    exact this.comp (measurable_pi_apply ℓ)
  -- Each summand is nonnegative.
  have h_summand_nn : ∀ b : ℕ → Bool, ∀ ℓ : ℕ,
      0 ≤ (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1) := by
    intro b ℓ
    apply div_nonneg _ (by positivity)
    split_ifs <;> norm_num
  -- Each summand is bounded above by (1/2)^(ℓ+1).
  have h_summand_le : ∀ b : ℕ → Bool, ∀ ℓ : ℕ,
      (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1) ≤
        (1 / 2 : ℝ) ^ (ℓ + 1) := by
    intro b ℓ
    rw [div_pow, one_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    split_ifs <;> norm_num
  have h_geom_summable : Summable (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1)) := by
    have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact h.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  have h_summable : ∀ b : ℕ → Bool, Summable (fun ℓ : ℕ =>
      (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1)) := by
    intro b
    exact Summable.of_nonneg_of_le (h_summand_nn b) (h_summand_le b) h_geom_summable
  -- Lift to ENNReal for measurability of the tsum.
  have h_eq : apssvT_factored P =
      fun b => (∑' ℓ, ENNReal.ofReal
        ((if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1))).toReal := by
    funext b
    rw [show apssvT_factored P b = ∑' ℓ,
        (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1) from rfl]
    rw [← ENNReal.ofReal_tsum_of_nonneg (h_summand_nn b) (h_summable b)]
    rw [ENNReal.toReal_ofReal (tsum_nonneg (h_summand_nn b))]
  rw [h_eq]
  apply Measurable.ennreal_toReal
  exact Measurable.ennreal_tsum
    (fun ℓ => ENNReal.measurable_ofReal.comp (h_summand_meas ℓ))

/-- Pair-indexing of the long-prefix coordinate sets for a pair `(w, w')`:
$$ \text{apssvT\_pairIndex}\,w\,w'\,P\,(b, \ell) :=
   \begin{cases}
     \text{apssvWordPrefix}\,w\,r \mathbin{+\!\!+} \text{apssvPrefix}\,P\,\ell & b = \text{false} \\
     \text{apssvWordPrefix}\,w'\,r \mathbin{+\!\!+} \text{apssvPrefix}\,P\,\ell & b = \text{true.}
   \end{cases} $$
This bundles the two coordinate sequences (one for `w`, one for `w'`) into a
single `Bool × ℕ`-indexed family for use with `iIndepFun.precomp`. -/
@[category API, AMS 11]
def apssvT_pairIndex {r : ℕ} (w w' : Fin r → Bool) (P : ℕ) :
    Bool × ℕ → List Bool := fun ⟨b, ℓ⟩ =>
  apssvWordPrefix (if b then w' else w) r ++ apssvPrefix P ℓ

/-- For `w ≠ w'`, the pairing `apssvT_pairIndex w w' P` is injective into
`List Bool`. Combines length comparison (forces equal `ℓ`) with
`apssvWordPrefix_injective` (forces equal `b` choice given that the
`apssvWordPrefix · r` slice agrees, and `w ≠ w'`). -/
@[category API, AMS 11]
lemma apssvT_pairIndex_injective {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w') (P : ℕ) :
    Function.Injective (apssvT_pairIndex w w' P) := by
  rintro ⟨b₁, ℓ₁⟩ ⟨b₂, ℓ₂⟩ h
  -- The pairing is `(b, ℓ) ↦ apssvWordPrefix (if b then w' else w) r ++ apssvPrefix P ℓ`.
  have h' : apssvWordPrefix (if b₁ then w' else w) r ++ apssvPrefix P ℓ₁ =
            apssvWordPrefix (if b₂ then w' else w) r ++ apssvPrefix P ℓ₂ := h
  -- Length comparison forces ℓ₁ = ℓ₂.
  have h_len : (apssvWordPrefix (if b₁ then w' else w) r ++ apssvPrefix P ℓ₁).length =
      (apssvWordPrefix (if b₂ then w' else w) r ++ apssvPrefix P ℓ₂).length :=
    congr_arg _ h'
  rw [List.length_append, List.length_append, apssvWordPrefix_length,
      apssvWordPrefix_length, apssvPrefix_length, apssvPrefix_length] at h_len
  have h_ℓ : ℓ₁ = ℓ₂ := by omega
  subst h_ℓ
  -- Take the first r elements: the apssvWordPrefix · r slices must be equal.
  have h_take : apssvWordPrefix (if b₁ then w' else w) r =
      apssvWordPrefix (if b₂ then w' else w) r := by
    have := congr_arg (List.take r) h'
    rwa [List.take_left' (apssvWordPrefix_length _ r),
         List.take_left' (apssvWordPrefix_length _ r)] at this
  -- Case-split on (b₁, b₂); when same, the Prod fst components agree; when different,
  -- apssvWordPrefix_injective with h_take gives w = w' (false ≠ true case) — contradicts hww'.
  rcases b₁ <;> rcases b₂
  · rfl
  · exact (hww' (apssvWordPrefix_injective (by simpa using h_take))).elim
  · exact (hww' (apssvWordPrefix_injective (by simpa using h_take)).symm).elim
  · rfl

/-- Reciprocal-form of `apssvJ`: dividing by $2^r$ gives the sum
$\sum_{i=0}^{r-1} (w_i \oplus \eta(\mathrm{prefix}_i))/2^{i+1}$, the "first $r$ digits"
of the binary expansion. -/
@[category API, AMS 11]
lemma apssvJ_div_two_pow (η : List Bool → Bool) (r : ℕ) (w : Fin r → Bool) :
    ((apssvJ η r w : ℝ) / (2 : ℝ) ^ r) =
      ∑ i ∈ Finset.range r,
        (if h : i < r then
          if (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) then (1 : ℝ) else 0
        else 0) / (2 : ℝ) ^ (i + 1) := by
  unfold apssvJ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  -- LHS at i: (if h : i<r then if b then 2^(r-1-i) else 0 else 0 : ℝ) / 2^r
  -- RHS at i: (if h : i<r then if b then 1 else 0 else 0) / 2^(i+1)
  rw [dif_pos hi, dif_pos hi]
  split_ifs with h_xor
  · -- 2^(r-1-i) / 2^r = 1 / 2^(i+1).
    have h_pow : ((2 : ℝ) ^ (r - 1 - i)) / (2 : ℝ) ^ r = (1 : ℝ) / (2 : ℝ) ^ (i + 1) := by
      have h_ne : (2 : ℝ) ^ r ≠ 0 := by positivity
      have h_ne₂ : (2 : ℝ) ^ (i + 1) ≠ 0 := by positivity
      rw [div_eq_div_iff h_ne h_ne₂]
      rw [one_mul, ← pow_add]
      congr 1
      omega
    push_cast
    exact h_pow
  · simp

/-- Bits of `P · 2^r + m` for `m < 2^r`: the first `r` bits come from `m`,
the remaining bits come from `P`. -/
@[category API, AMS 11]
lemma apssv_testBit_block (P r m : ℕ) (hm : m < 2 ^ r) (i : ℕ) :
    (P * 2 ^ r + m).testBit i =
      if i < r then m.testBit i else P.testBit (i - r) := by
  rw [Nat.mul_comm P (2 ^ r), Nat.testBit_two_pow_mul_add (a := P) hm i]

/-- The `apssvPrefix` of `P · 2^r + m` for `i ≤ r` is the `apssvWordPrefix` of `w`,
where `w` is the bit decomposition of `m`. -/
@[category API, AMS 11]
lemma apssvPrefix_block_le_r {P r m : ℕ} (hm : m < 2 ^ r) (w : Fin r → Bool)
    (hw : ∀ i : Fin r, w i = m.testBit i) :
    ∀ i : ℕ, i ≤ r → apssvPrefix (P * 2 ^ r + m) i = apssvWordPrefix w i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i ≤ r := by omega
    have hi_lt : i < r := by omega
    rw [apssvPrefix_succ, ih hi']
    -- Need: apssvWordPrefix w i ++ [(P*2^r+m).testBit i] = apssvWordPrefix w (i+1).
    rw [apssv_testBit_block P r m hm i, if_pos hi_lt]
    show apssvWordPrefix w i ++ [m.testBit i] = _
    show apssvWordPrefix w i ++ [m.testBit i] =
        apssvWordPrefix w i ++ [if h : i < r then w ⟨i, h⟩ else false]
    rw [dif_pos hi_lt]
    have : w ⟨i, hi_lt⟩ = m.testBit i := hw ⟨i, hi_lt⟩
    rw [this]

/-- The `apssvPrefix` of `P · 2^r + m` for `i = r + ℓ` decomposes as
`apssvWordPrefix w r ++ apssvPrefix P ℓ`. -/
@[category API, AMS 11]
lemma apssvPrefix_block_ge_r {P r m : ℕ} (hm : m < 2 ^ r) (w : Fin r → Bool)
    (hw : ∀ i : Fin r, w i = m.testBit i) :
    ∀ ℓ : ℕ, apssvPrefix (P * 2 ^ r + m) (r + ℓ) =
      apssvWordPrefix w r ++ apssvPrefix P ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    rw [Nat.add_zero]
    rw [apssvPrefix_block_le_r hm w hw r (le_refl _)]
    show apssvWordPrefix w r = apssvWordPrefix w r ++ apssvPrefix P 0
    rw [apssvPrefix_zero, List.append_nil]
  | succ ℓ ih =>
    -- (r + ℓ + 1) bits = first (r+ℓ) bits ++ [bit (r+ℓ)].
    rw [show r + (ℓ + 1) = (r + ℓ) + 1 from by ring]
    rw [apssvPrefix_succ, ih]
    rw [apssv_testBit_block P r m hm (r + ℓ)]
    have h_not_lt : ¬ (r + ℓ < r) := by omega
    rw [if_neg h_not_lt]
    have h_sub : r + ℓ - r = ℓ := by omega
    rw [h_sub, apssvPrefix_succ]
    -- (a ++ b) ++ [x] = a ++ (b ++ [x])
    rw [List.append_assoc]

/-- The block-sum building block of [APSSV26b §3, eq. (3.4)]:
$$ B_{P,r}(k) := \sum_{w \in \{0,1\}^r} e\!\left(\,k \!\cdot\! \frac{j_r(w) + T_{w,P}}{2^r}\right). $$
Sums the additive character `e(k · ·)` over all $2^r$ scrambled prefix-tails. -/
@[category API, AMS 11]
noncomputable def apssvBlockSum (η : List Bool → Bool) (P r : ℕ) (k : ℕ) : ℂ :=
  ∑ w : (Fin r → Bool), e ((k : ℝ) *
    ((apssvJ η r w : ℝ) + apssvT η w P) / (2 : ℝ) ^ r)

/-- Proposition 3.4 of [APSSV26b §3]: block decomposition.

For $n = P \cdot 2^r + m$ with $m \in [0, 2^r)$ having bits $w_0, \ldots, w_{r-1}$,
$$ x_n = \frac{j_r(w) + T_{w,P}}{2^r}. $$
Consequently, the exponential sum over the dyadic block factors as
$$ \sum_{n = P \cdot 2^r}^{(P+1) 2^r - 1} e(k \cdot x_n) = B_{P,r}(k). $$

**Proof outline** (the implementation: tsum manipulation):
1. Split the tsum defining `apssvX η n` at index `r` (the first `r` digits are
   determined by `m`'s bits, the tail by `P`'s bits).
2. The first `r` terms reorganize to `apssvJ η r w / 2^r` since
   `j_r(w) = ∑ b_i · 2^{r-1-i}` and `j_r(w)/2^r = ∑ b_i / 2^{i+1}`.
3. The tail (indices `≥ r`) factors out `1/2^r` and equals `apssvT η w P / 2^r`.
4. Summing over $m \in \{0,\ldots,2^r-1\}$ and bijecting via `apssvJ_bijective`
   gives the block-sum identity. -/
@[category API, AMS 11]
lemma apssvX_block_eq (η : List Bool → Bool) (P r : ℕ) (m : ℕ) (hm : m < 2 ^ r)
    (w : Fin r → Bool)
    (hw : ∀ i : Fin r, w i = m.testBit i) :
    apssvX η (P * 2 ^ r + m) =
      ((apssvJ η r w : ℝ) + apssvT η w P) / (2 : ℝ) ^ r := by
  -- Split the tsum at index r.
  let n : ℕ := P * 2 ^ r + m
  have h_split : apssvX η n = (∑ i ∈ Finset.range r,
      (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) /
        (2 : ℝ) ^ (i + 1)) +
      ∑' ℓ : ℕ, (if (n.testBit (ℓ + r)).xor (η (apssvPrefix n (ℓ + r))) then (1 : ℝ) else 0) /
        (2 : ℝ) ^ ((ℓ + r) + 1) := by
    show ∑' i, _ = _
    have h_summable := apssvX_summable η n
    have := h_summable.sum_add_tsum_nat_add r
    rw [show (fun i : ℕ =>
        (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) /
          (2 : ℝ) ^ (i + 1)) = (fun i : ℕ =>
        (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) /
          (2 : ℝ) ^ (i + 1)) from rfl]
    rw [← this]
  rw [h_split]
  -- The first r terms = apssvJ η r w / 2^r.
  have h_first : (∑ i ∈ Finset.range r,
      (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) /
        (2 : ℝ) ^ (i + 1)) = (apssvJ η r w : ℝ) / (2 : ℝ) ^ r := by
    rw [apssvJ_div_two_pow]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    -- testBit i of n = w_i (using hw and apssv_testBit_block).
    rw [apssv_testBit_block P r m hm i, if_pos hi]
    -- apssvPrefix n i = apssvWordPrefix w i.
    rw [apssvPrefix_block_le_r hm w hw i hi.le]
    -- The RHS unfolds the dif and replaces w ⟨i, hi⟩ by m.testBit i.
    rw [dif_pos hi]
    have : w ⟨i, hi⟩ = m.testBit i := hw ⟨i, hi⟩
    rw [this]
  -- The tail = apssvT η w P / 2^r.
  have h_tail : (∑' ℓ : ℕ, (if (n.testBit (ℓ + r)).xor (η (apssvPrefix n (ℓ + r))) then (1 : ℝ) else 0) /
        (2 : ℝ) ^ ((ℓ + r) + 1)) = apssvT η w P / (2 : ℝ) ^ r := by
    unfold apssvT
    rw [eq_div_iff (by positivity : (2 : ℝ) ^ r ≠ 0)]
    rw [← tsum_mul_right]
    refine tsum_congr fun ℓ => ?_
    -- The (ℓ+r)-th term of n is P.testBit ℓ.
    rw [show ℓ + r = r + ℓ from by ring, apssv_testBit_block P r m hm (r + ℓ)]
    have h_not_lt : ¬ (r + ℓ < r) := by omega
    rw [if_neg h_not_lt]
    have h_sub : r + ℓ - r = ℓ := by omega
    rw [h_sub]
    rw [apssvPrefix_block_ge_r hm w hw ℓ]
    -- 2^((r+ℓ)+1) = 2^(ℓ+1) · 2^r
    have h_pow_eq : ((2 : ℝ) ^ ((r + ℓ) + 1)) = (2 : ℝ) ^ (ℓ + 1) * (2 : ℝ) ^ r := by
      rw [← pow_add]; congr 1; omega
    rw [h_pow_eq]
    field_simp
  rw [h_first, h_tail]
  ring

/-- Bit-decoding bijection: `Fin (2^r) ≃ (Fin r → Bool)` via `m ↦ (fun i => m.testBit i)`. -/
@[category API, AMS 11]
def apssvBitDecode (r : ℕ) : Fin (2 ^ r) → (Fin r → Bool) :=
  fun m i => (m : ℕ).testBit i

/-- Bit-decoding is bijective. Injectivity uses `Nat.eq_of_testBit_eq` (combined with
`m < 2^r`); cardinality matches via `apssv_card_word_eq_two_pow`. -/
@[category API, AMS 11]
lemma apssvBitDecode_bijective (r : ℕ) : Function.Bijective (apssvBitDecode r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · -- Injective.
    intro m₁ m₂ h
    apply Fin.ext
    refine Nat.eq_of_testBit_eq ?_
    intro i
    by_cases hi : i < r
    · -- For i < r: testBit values match by hypothesis.
      have := congr_fun h ⟨i, hi⟩
      exact this
    · -- For i ≥ r: both testBit values are false (m_j < 2^r ≤ 2^i).
      push_neg at hi
      have hi_le : 2 ^ r ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le m₁.is_lt hi_le)]
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le m₂.is_lt hi_le)]
  · simp

/-- Block-sum identity (corollary of `apssvX_block_eq`): the partial-sum over a dyadic
block of length $2^r$ equals `apssvBlockSum`. Reindexes via the bit-decoding
bijection: `m ↦ (fun i => m.testBit i)`. -/
@[category API, AMS 11]
lemma apssv_block_sum_eq (η : List Bool → Bool) (P r : ℕ) (k : ℕ) :
    ∑ m ∈ Finset.range (2 ^ r), e ((k : ℝ) * apssvX η (P * 2 ^ r + m)) =
      apssvBlockSum η P r k := by
  unfold apssvBlockSum
  rw [Finset.sum_range]
  -- Bit-decoding equivalence φ : Fin (2^r) ≃ (Fin r → Bool).
  let φ : Fin (2 ^ r) ≃ (Fin r → Bool) :=
    Equiv.ofBijective _ (apssvBitDecode_bijective r)
  apply Fintype.sum_equiv φ
  intro m
  -- Apply apssvX_block_eq.
  have hm_lt : (m : ℕ) < 2 ^ r := m.is_lt
  rw [apssvX_block_eq η P r m hm_lt (φ m) (fun i => rfl)]
  ring_nf

/-- The "frequency scale" $b(k)$ from [APSSV26b §3.1]. Mathematically the paper uses
$\lceil \log_2(2k) \rceil$, but our formal definition is `Nat.log2 (2*k) + 1`, i.e.
$\lfloor \log_2(2k) \rfloor + 1$. These coincide except when $2k$ is a power of two,
in which case our `apssvB k` is one larger than the strict ceiling. The inflated
value only weakens the bound (a larger $b$ gives a larger envelope), so all downstream
arguments remain correct. The formal invariant is $2^{b-1} \le 2k < 2^b$ (hence
$2^b \le 4k$ — see `apssv_two_pow_b_le`). -/
@[category API, AMS 11]
def apssvB (k : ℕ) : ℕ := Nat.log2 (2 * k) + 1

/-- Auxiliary form of `apssv_dyadic_decomp` with an offset `S` aligned to a fixed
dyadic level `r+1`. Inducting on `r`, we peel off one bit of `N` at a time.

The statement exposes four invariants on the index set `T`:
* **Offset**: `S ≤ pr.1 * 2 ^ pr.2` — every block `[P · 2^ρ, (P+1) · 2^ρ)` starts at or
  after `S`. Used to ensure recursive disjointness.
* **Level bound**: `pr.2 ≤ r` — every level used is at most the recursion level.
* **Per-level multiplicity ≤ 2**: at most two blocks share the same level. Only level 0
  can have two (from the `N = 2` base case); all higher levels have at most one block.
  This bound is essential for the geometric envelope argument in `apssv_partial_sum_bound`.
* **Sum equality**: `∑_{n<N} e(k x_{S+n}) = ∑_{(P,ρ)∈T} apssvBlockSum η P ρ k`.

The N = 2 base case uses two level-0 blocks `{(S, 0), (S+1, 0)}` rather than one level-1
block `{(S/2, 1)}`. This keeps level 1 reserved for the `succ 0` recursion step, ensuring
multiplicity is at most 2 at level 0 and at most 1 elsewhere. -/
@[category API, AMS 11]
lemma apssv_dyadic_decomp_aux (η : List Bool → Bool) (k : ℕ) :
    ∀ (r N S : ℕ), N ≤ 2 ^ (r + 1) → 2 ^ (r + 1) ∣ S →
      ∃ (T : Finset (ℕ × ℕ)),
        (∀ pr ∈ T, S ≤ pr.1 * 2 ^ pr.2) ∧
        (∀ pr ∈ T, pr.2 ≤ r) ∧
        (∀ ρ : ℕ, (T.filter fun pr => pr.2 = ρ).card ≤ 2) ∧
        ∑ n ∈ Finset.range N, e ((k : ℝ) * apssvX η (S + n)) =
          ∑ pr ∈ T, apssvBlockSum η pr.1 pr.2 k := by
  intro r
  induction r with
  | zero =>
    -- Base: 2^(0+1) = 2; N ≤ 2 has cases N = 0, 1, 2.
    intro N S hN hS
    interval_cases N
    · refine ⟨∅, by simp, by simp, by simp, by simp⟩
    · -- N = 1: T = {(S, 0)}.
      refine ⟨{(S, 0)}, ?_, ?_, ?_, ?_⟩
      · intro pr hpr
        rw [Finset.mem_singleton] at hpr
        subst hpr
        simp
      · intro pr hpr
        rw [Finset.mem_singleton] at hpr
        subst hpr
        exact Nat.zero_le _
      · intro ρ
        by_cases h : ρ = 0
        · subst h
          calc (({(S, 0)} : Finset (ℕ × ℕ)).filter (fun pr => pr.2 = 0)).card
              ≤ ({(S, 0)} : Finset (ℕ × ℕ)).card := Finset.card_filter_le _ _
            _ = 1 := by simp
            _ ≤ 2 := by omega
        · have : ({(S, 0)} : Finset (ℕ × ℕ)).filter (fun pr => pr.2 = ρ) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro pr hpr
            rw [Finset.mem_singleton] at hpr
            subst hpr
            exact fun heq => h heq.symm
          rw [this]; simp
      · have hbs := apssv_block_sum_eq η S 0 k
        simp only [pow_zero, Finset.sum_range_one, mul_one, add_zero] at hbs
        simp only [Finset.sum_range_one, Finset.sum_singleton, add_zero]
        exact hbs
    · -- N = 2: T = {(S, 0), (S+1, 0)} — TWO level-0 blocks (not one level-1 block).
      refine ⟨{(S, 0), (S+1, 0)}, ?_, ?_, ?_, ?_⟩
      · intro pr hpr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpr
        rcases hpr with rfl | rfl
        · simp
        · simp
      · intro pr hpr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpr
        rcases hpr with rfl | rfl
        · exact Nat.zero_le _
        · exact Nat.zero_le _
      · intro ρ
        by_cases hρ : ρ = 0
        · subst hρ
          have : ({(S, 0), (S+1, 0)} : Finset (ℕ × ℕ)).filter (fun pr => pr.2 = 0)
                = {(S, 0), (S+1, 0)} := by
            apply Finset.filter_eq_self.mpr
            intro pr hpr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hpr
            rcases hpr with rfl | rfl <;> rfl
          rw [this]
          have hcard : ({(S, 0), (S+1, 0)} : Finset (ℕ × ℕ)).card ≤ 2 := by
            apply le_trans (Finset.card_insert_le _ _)
            simp
          exact hcard
        · have : ({(S, 0), (S+1, 0)} : Finset (ℕ × ℕ)).filter (fun pr => pr.2 = ρ) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro pr hpr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hpr
            rcases hpr with rfl | rfl <;> exact fun heq => hρ heq.symm
          rw [this]; simp
      · -- Sum equality: ∑_{n<2} e(k x_{S+n}) = e(k x_S) + e(k x_{S+1}).
        have hne : ((S, 0) : ℕ × ℕ) ≠ (S + 1, 0) := by
          intro h
          have : S = S + 1 := (Prod.mk.injEq _ _ _ _).mp h |>.1
          omega
        rw [show ({(S, 0), (S + 1, 0)} : Finset (ℕ × ℕ)) = insert (S, 0) {(S + 1, 0)} from rfl]
        rw [Finset.sum_insert (by simp [hne])]
        rw [Finset.sum_singleton]
        have hbsS := apssv_block_sum_eq η S 0 k
        have hbsS1 := apssv_block_sum_eq η (S + 1) 0 k
        simp only [pow_zero, Finset.sum_range_one, mul_one, add_zero] at hbsS hbsS1
        rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
            ← hbsS, ← hbsS1]
        rw [Nat.add_zero]
  | succ r ih =>
    intro N S hN hS
    by_cases hNle : N ≤ 2 ^ (r + 1)
    · -- Recurse at level r with the same N, S.
      have hSr : 2 ^ (r + 1) ∣ S := by
        have hpow : 2 ^ (r + 1) ∣ 2 ^ (r + 1 + 1) :=
          pow_dvd_pow 2 (by omega)
        exact dvd_trans hpow hS
      obtain ⟨T, hT_off, hT_lev, hT_mult, hT_eq⟩ := ih N S hNle hSr
      refine ⟨T, hT_off, ?_, hT_mult, hT_eq⟩
      intro pr hpr
      exact (hT_lev pr hpr).trans (Nat.le_succ _)
    · -- 2^(r+1) < N; split [0, N) = [0, 2^(r+1)) ⊔ [2^(r+1), N).
      push_neg at hNle
      set R : ℕ := r + 1 with hR_def
      have hR_pow_pos : 0 < (2 : ℕ) ^ R := Nat.two_pow_pos R
      have hN_split : N = 2 ^ R + (N - 2 ^ R) := by omega
      have hN_minus_le : N - 2 ^ R ≤ 2 ^ R := by
        have h2R_succ : (2 : ℕ) ^ (R + 1) = 2 ^ R + 2 ^ R := by
          rw [pow_succ]; ring
        rw [h2R_succ] at hN
        omega
      have hSR : 2 ^ R ∣ S := by
        have hpow : (2 : ℕ) ^ R ∣ 2 ^ (R + 1) :=
          pow_dvd_pow 2 (by omega)
        exact dvd_trans hpow hS
      have hSR' : 2 ^ R ∣ (S + 2 ^ R) :=
        Nat.dvd_add hSR (dvd_refl _)
      -- Split the range sum: range N = range 2^R + (translated) range (N - 2^R).
      have h_rangesplit :
          ∑ n ∈ Finset.range N, e ((k : ℝ) * apssvX η (S + n)) =
            (∑ n ∈ Finset.range (2 ^ R), e ((k : ℝ) * apssvX η (S + n))) +
              ∑ n ∈ Finset.range (N - 2 ^ R), e ((k : ℝ) * apssvX η (S + 2 ^ R + n)) := by
        conv_lhs => rw [hN_split]
        rw [Finset.sum_range_add]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        congr 2
        ring_nf
      -- First half = apssvBlockSum η (S / 2^R) R k.
      have hS_div : S / 2 ^ R * 2 ^ R = S := Nat.div_mul_cancel hSR
      have h_firsthalf :
          ∑ n ∈ Finset.range (2 ^ R), e ((k : ℝ) * apssvX η (S + n)) =
            apssvBlockSum η (S / 2 ^ R) R k := by
        rw [← apssv_block_sum_eq η (S / 2 ^ R) R k]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hS_div]
      -- IH for the tail at level r+1 = R, offset S + 2^R.
      obtain ⟨T', hT'_off, hT'_lev, hT'_mult, hT'_eq⟩ :=
        ih (N - 2 ^ R) (S + 2 ^ R) hN_minus_le hSR'
      -- The new block (S / 2^R, R) is at level R = r+1 > r ≥ all levels in T'.
      have h_new_notmem : (S / 2 ^ R, R) ∉ T' := by
        intro hmem
        have hlev := hT'_lev _ hmem
        simp at hlev
        omega
      refine ⟨insert (S / 2 ^ R, R) T', ?_, ?_, ?_, ?_⟩
      · -- Offset invariant.
        intro pr hpr
        rw [Finset.mem_insert] at hpr
        cases hpr with
        | inl h =>
          subst h
          simp only [hS_div]; exact le_refl _
        | inr h =>
          have hge := hT'_off _ h
          omega
      · -- Level bound: pr.2 ≤ r+1 (= R = succ r).
        intro pr hpr
        rw [Finset.mem_insert] at hpr
        cases hpr with
        | inl h => subst h; exact le_refl _
        | inr h => exact (hT'_lev pr h).trans (Nat.le_succ _)
      · -- Multiplicity ≤ 2 at every level.
        intro ρ
        by_cases hρR : ρ = R
        · -- At level R, T' has no blocks; only the new (S/2^R, R) is added.
          have hfilter :
              (insert (S / 2 ^ R, R) T').filter (fun pr => pr.2 = ρ) =
                {(S / 2 ^ R, R)} := by
            ext pr
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hmem, hlev⟩
              cases hmem with
              | inl h => exact h
              | inr h =>
                exfalso
                have := hT'_lev pr h
                rw [hlev, hρR] at this
                omega
            · intro h
              subst h
              exact ⟨Or.inl rfl, hρR.symm⟩
          rw [hfilter]; simp
        · -- At level ρ ≠ R, only T' contributes; mult ≤ 2 from IH.
          have hfilter :
              (insert (S / 2 ^ R, R) T').filter (fun pr => pr.2 = ρ) =
                T'.filter (fun pr => pr.2 = ρ) := by
            ext pr
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hmem, hlev⟩
              cases hmem with
              | inl h => exfalso; subst h; exact hρR hlev.symm
              | inr h => exact ⟨h, hlev⟩
            · rintro ⟨h, hlev⟩; exact ⟨Or.inr h, hlev⟩
          rw [hfilter]
          exact hT'_mult ρ
      · rw [h_rangesplit, h_firsthalf, hT'_eq, Finset.sum_insert h_new_notmem]

/-- The dyadic decomposition of $[0, N)$: writing $N$ in binary as $N = \sum_i b_i 2^i$,
the partial sum $\sum_{n < N} e(k \cdot x_n)$ decomposes as a sum of `apssvBlockSum`.
The index set `T` satisfies a per-level multiplicity ≤ 2 invariant (essential for the
geometric envelope argument in `apssv_partial_sum_bound`) and a level bound `pr.2 ≤ N`.

Proved via the auxiliary `apssv_dyadic_decomp_aux`, instantiated at offset `S = 0`
and level `r` such that `N ≤ 2 ^ (r + 1)` (concretely, take `r = N`). -/
@[category API, AMS 11]
lemma apssv_dyadic_decomp (η : List Bool → Bool) (k N : ℕ) :
    ∃ (T : Finset (ℕ × ℕ)),
      (∀ pr ∈ T, pr.2 ≤ N) ∧
      (∀ ρ : ℕ, (T.filter fun pr => pr.2 = ρ).card ≤ 2) ∧
      ∑ n ∈ Finset.range N, e ((k : ℝ) * apssvX η n) =
        ∑ pr ∈ T, apssvBlockSum η pr.1 pr.2 k := by
  -- Apply the aux lemma with S = 0 and a sufficiently large level r.
  have hN_le : N ≤ 2 ^ (N + 1) := by
    have := Nat.lt_two_pow_self (n := N + 1)
    omega
  have hS_dvd : (2 : ℕ) ^ (N + 1) ∣ 0 := dvd_zero _
  obtain ⟨T, _, hT_lev, hT_mult, hT_eq⟩ := apssv_dyadic_decomp_aux η k N N 0 hN_le hS_dvd
  refine ⟨T, hT_lev, hT_mult, ?_⟩
  rw [← hT_eq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.zero_add]

/-- The block-bound predicate from [APSSV26b Proposition 3.5]: for some absolute constant `C`,
$$ |B_{P, r}(k)| \le C \cdot \sqrt{r + b} \cdot \min\{2^{r/2},\; 2^{b - r/2}\} $$
for all $P, r$, where $b = b(k)$ is `apssvB k` (formally `Nat.log2 (2k) + 1`,
i.e. $\lfloor \log_2(2k) \rfloor + 1$ — see `apssvB`'s docstring; this differs from
the strict ceiling at exact powers of two but only by 1, which weakens the bound
harmlessly). The min-formula expresses the two regimes: short blocks (`r ≤ b`) and
long blocks (`r > b`).

A specific scrambling function $\eta$ "satisfies the block bound" (with constant $C$) if the
above holds for all $P, r$. By [APSSV26b Prop 3.5], a *random* $\eta$ satisfies it with
positive probability — hence a deterministic such $\eta$ exists. -/
@[category API, AMS 11]
def apssvBlockBound (η : List Bool → Bool) (C : ℝ) : Prop :=
  ∀ k P r : ℕ, 1 ≤ k →
    ‖apssvBlockSum η P r k‖ ≤
      C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))
/- ## Probability infrastructure for `apssv_exists_block_bound` -/

/-- Bernoulli(1/2) PMF on `Bool`. -/
@[category API, AMS 11]
noncomputable def apssvBoolPMF : PMF Bool := PMF.bernoulli (1/2) (by norm_num)

/-- Bernoulli(1/2) measure on `Bool`. -/
@[category API, AMS 11]
noncomputable def apssvBoolMeasure : MeasureTheory.Measure Bool := apssvBoolPMF.toMeasure

instance : MeasureTheory.IsProbabilityMeasure apssvBoolMeasure := by
  unfold apssvBoolMeasure
  exact PMF.toMeasure.isProbabilityMeasure _

/-- Probability measure on `List Bool → Bool`: i.i.d. Bernoulli(1/2) at each finite
binary word. Used as the random construction underlying the APSSV block bound. -/
@[category API, AMS 11]
noncomputable def apssvEtaMeasure : MeasureTheory.Measure (List Bool → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : List Bool => apssvBoolMeasure)

instance : MeasureTheory.IsProbabilityMeasure apssvEtaMeasure := by
  unfold apssvEtaMeasure
  infer_instance

/-- The coordinate map `η ↦ η u` from `List Bool → Bool` to `Bool` is measurable. -/
@[category API, AMS 11]
lemma apssv_eta_coord_measurable (u : List Bool) :
    Measurable (fun η : List Bool → Bool => η u) :=
  measurable_pi_apply u

/-- `apssvJ η r w` is measurable in `η`. It is a finite sum (over `Finset.range r`)
of `ℕ`-valued indicator-style summands, each depending on `η` at a single
coordinate `apssvWordPrefix w i`. -/
@[category API, AMS 11]
lemma apssvJ_measurable (r : ℕ) (w : Fin r → Bool) :
    Measurable (fun η : List Bool → Bool => apssvJ η r w) := by
  unfold apssvJ
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : i < r
  · simp only [h, dite_true]
    -- η ↦ if (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) then 2^(r-1-i) else 0
    refine Measurable.ite ?_ measurable_const measurable_const
    -- {η | (w ⟨i, h⟩).xor (η (apssvWordPrefix w i)) = true} is measurable.
    have h_xor_meas : Measurable
        (fun η : List Bool → Bool => (w ⟨i, h⟩).xor (η (apssvWordPrefix w i))) := by
      have h1 : Measurable (fun η : List Bool → Bool => η (apssvWordPrefix w i)) :=
        apssv_eta_coord_measurable _
      have h2 : Measurable (fun b : Bool => (w ⟨i, h⟩).xor b) :=
        measurable_of_countable _
      exact h2.comp h1
    exact h_xor_meas (measurableSet_singleton true)
  · simp only [h, dite_false]
    exact measurable_const

/- ## Short-coords σ-algebra (conditioning σ-algebra for the MGF chassis)

The conditional sub-Gaussian MGF argument for `apssvBlockSum.re`/`.im` conditions on the
σ-algebra generated by the η-coordinates at "short" prefixes (positions `c : List Bool`
with `c.length < r`). Under this conditioning, `apssvJ η r w` (and hence the per-summand
factor `c_w(η) := e(k · apssvJ η r w / 2^r)`) is constant, while `apssvT η w P` (and
hence `Y_w(η) := e(k · apssvT η w P / 2^r)`) lives on the disjoint long-coords slice and
inherits its full unconditional joint distribution. This split is the structural input
to `HasCondSubgaussianMGF` (Mathlib `Probability/Moments/SubGaussian.lean`). -/

/-- The σ-algebra of short η-coordinates: the sub-σ-algebra of
`MeasurableSpace (List Bool → Bool)` generated by the projection maps `η ↦ η c` for
`c : List Bool` with `c.length < r`.

Used as the conditioning σ-algebra in the conditional sub-Gaussian MGF chassis for the
APSSV block sum: `apssvJ η r w` — a finite sum over `i ∈ Finset.range r` of summands
each depending on `η` at the coordinate `apssvWordPrefix w i` (length `i < r`) — is
`apssvShortSigma r`-measurable. -/
@[category API, AMS 11]
def apssvShortSigma (r : ℕ) : MeasurableSpace (List Bool → Bool) :=
  ⨆ c : {c : List Bool // c.length < r},
    MeasurableSpace.comap (fun η : List Bool → Bool => η c.val) inferInstance

/-- `apssvShortSigma r` is a sub-σ-algebra of the canonical product σ-algebra on
`List Bool → Bool`. Each summand `comap (fun η ↦ η c) inferInstance` is dominated by
the canonical σ-algebra (since `η ↦ η c` is measurable, by `apssv_eta_coord_measurable`);
the supremum inherits this. -/
@[category API, AMS 11]
lemma apssvShortSigma_le (r : ℕ) :
    apssvShortSigma r ≤ (inferInstance : MeasurableSpace (List Bool → Bool)) := by
  refine iSup_le fun c => ?_
  exact (apssv_eta_coord_measurable c.val).comap_le

/-- For any `c : List Bool` with `c.length < r`, the projection `η ↦ η c` is
measurable with respect to `apssvShortSigma r`. Direct from `le_iSup_of_le` with
the bundled index `⟨c, hc⟩`. -/
@[category API, AMS 11]
lemma apssv_eta_coord_apssvShortSigma_measurable (r : ℕ) (c : List Bool) (hc : c.length < r) :
    @Measurable _ _ (apssvShortSigma r) _ (fun η : List Bool → Bool => η c) := by
  letI : MeasurableSpace (List Bool → Bool) := apssvShortSigma r
  refine Measurable.of_comap_le ?_
  exact le_iSup_of_le (⟨c, hc⟩ : {c : List Bool // c.length < r}) le_rfl

/-- `apssvJ η r w` is `apssvShortSigma r`-measurable: a finite sum over
`i ∈ Finset.range r` of indicator-style summands, each depending on `η` at the
coordinate `apssvWordPrefix w i`, whose length `i` is `< r` (by
`apssvWordPrefix_length`). -/
@[category API, AMS 11]
lemma apssvJ_apssvShortSigma_measurable (r : ℕ) (w : Fin r → Bool) :
    @Measurable _ _ (apssvShortSigma r) _ (fun η : List Bool → Bool => apssvJ η r w) := by
  letI : MeasurableSpace (List Bool → Bool) := apssvShortSigma r
  unfold apssvJ
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : i < r
  · simp only [h, dite_true]
    refine Measurable.ite ?_ measurable_const measurable_const
    have h_prefix_len : (apssvWordPrefix w i).length < r := by
      rw [apssvWordPrefix_length]; exact h
    have h_coord : Measurable (fun η : List Bool → Bool => η (apssvWordPrefix w i)) :=
      apssv_eta_coord_apssvShortSigma_measurable r _ h_prefix_len
    have h_xor : Measurable (fun b : Bool => (w ⟨i, h⟩).xor b) := measurable_of_countable _
    exact (h_xor.comp h_coord) (measurableSet_singleton true)
  · simp only [h, dite_false]
    exact measurable_const

/-- The complex Fourier weight `c_w(η) := e(k · apssvJ η r w / 2^r)` is
`apssvShortSigma r`-measurable. Direct composition of `apssvJ_apssvShortSigma_measurable`
with the (continuous) ℕ-cast and the (continuous) `e ∘ (· * k / 2^r)` map. -/
@[category API, AMS 11]
lemma apssvBlockSum_c_apssvShortSigma_measurable (r : ℕ) (w : Fin r → Bool) (k : ℕ) :
    @Measurable _ _ (apssvShortSigma r) _
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) := by
  letI : MeasurableSpace (List Bool → Bool) := apssvShortSigma r
  have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
  have h_J : Measurable (fun η : List Bool → Bool => apssvJ η r w) :=
    apssvJ_apssvShortSigma_measurable r w
  have h_J_real : Measurable (fun η : List Bool → Bool => (apssvJ η r w : ℝ)) :=
    h_natCast_real.comp h_J
  have h_outer : Measurable (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) := by
    have h_cont : Continuous (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) := by
      unfold e
      exact Complex.continuous_exp.comp (by continuity)
    exact h_cont.measurable
  exact h_outer.comp h_J_real

/-- The σ-algebra of long η-coordinates: the sub-σ-algebra of
`MeasurableSpace (List Bool → Bool)` generated by the projection maps `η ↦ η c` for
`c : List Bool` with `r ≤ c.length`.

Symmetric to `apssvShortSigma r`. Used in the conditional sub-Gaussian MGF chassis to
locate the (Y_w)_w family: each `apssvT η w P` involves only η-coords at positions
`apssvWordPrefix w r ++ apssvPrefix P ℓ` (length `r + ℓ ≥ r`), so it is
`apssvLongSigma r`-measurable. The independence of `apssvShortSigma r` and
`apssvLongSigma r` (under the iid product measure `apssvEtaMeasure`) is the core
structural input to the conditional independence of c_w from (Y_w)_w. -/
@[category API, AMS 11]
def apssvLongSigma (r : ℕ) : MeasurableSpace (List Bool → Bool) :=
  ⨆ c : {c : List Bool // r ≤ c.length},
    MeasurableSpace.comap (fun η : List Bool → Bool => η c.val) inferInstance

/-- `apssvLongSigma r` is a sub-σ-algebra of the canonical product σ-algebra on
`List Bool → Bool`. Symmetric to `apssvShortSigma_le`. -/
@[category API, AMS 11]
lemma apssvLongSigma_le (r : ℕ) :
    apssvLongSigma r ≤ (inferInstance : MeasurableSpace (List Bool → Bool)) := by
  refine iSup_le fun c => ?_
  exact (apssv_eta_coord_measurable c.val).comap_le

/-- For any `c : List Bool` with `r ≤ c.length`, the projection `η ↦ η c` is
measurable with respect to `apssvLongSigma r`. -/
@[category API, AMS 11]
lemma apssv_eta_coord_apssvLongSigma_measurable (r : ℕ) (c : List Bool) (hc : r ≤ c.length) :
    @Measurable _ _ (apssvLongSigma r) _ (fun η : List Bool → Bool => η c) := by
  letI : MeasurableSpace (List Bool → Bool) := apssvLongSigma r
  refine Measurable.of_comap_le ?_
  exact le_iSup_of_le (⟨c, hc⟩ : {c : List Bool // r ≤ c.length}) le_rfl

/-- `apssvT η w P` is `apssvLongSigma r`-measurable: `apssvT η w P = ∑'ℓ, ...` involves
η at positions `apssvWordPrefix w r ++ apssvPrefix P ℓ`, each of length `r + ℓ ≥ r`
(by `apssvWordPrefix_length` and `apssvPrefix_length`). -/
@[category API, AMS 11]
lemma apssvT_apssvLongSigma_measurable {r : ℕ} (w : Fin r → Bool) (P : ℕ) :
    @Measurable _ _ (apssvLongSigma r) _ (fun η : List Bool → Bool => apssvT η w P) := by
  letI : MeasurableSpace (List Bool → Bool) := apssvLongSigma r
  -- η ↦ apssvT η w P = apssvT_factored P ∘ (η ↦ ℓ ↦ η (apssvWordPrefix w r ++ apssvPrefix P ℓ)).
  have h_eq : (fun η : List Bool → Bool => apssvT η w P) =
      apssvT_factored P ∘
        fun η : List Bool → Bool => fun ℓ => η (apssvWordPrefix w r ++ apssvPrefix P ℓ) := by
    funext η
    exact apssvT_eq_factored η w P
  rw [h_eq]
  apply (apssvT_factored_measurable P).comp
  apply measurable_pi_lambda
  intro ℓ
  -- η ↦ η (apssvWordPrefix w r ++ apssvPrefix P ℓ) is apssvLongSigma r-measurable
  -- since the coord has length r + ℓ ≥ r.
  refine apssv_eta_coord_apssvLongSigma_measurable r _ ?_
  rw [List.length_append, apssvWordPrefix_length, apssvPrefix_length]
  exact Nat.le_add_right _ _

/-- The complex Fourier weight `Y_w(η) := e(k · apssvT η w P / 2^r)` is
`apssvLongSigma r`-measurable. Symmetric to `apssvBlockSum_c_apssvShortSigma_measurable`. -/
@[category API, AMS 11]
lemma apssvBlockSum_Y_apssvLongSigma_measurable {r : ℕ} (w : Fin r → Bool) (P k : ℕ) :
    @Measurable _ _ (apssvLongSigma r) _
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := by
  letI : MeasurableSpace (List Bool → Bool) := apssvLongSigma r
  have h_T : Measurable (fun η : List Bool → Bool => apssvT η w P) :=
    apssvT_apssvLongSigma_measurable w P
  have h_outer : Measurable (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) := by
    have h_cont : Continuous (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) := by
      unfold e
      exact Complex.continuous_exp.comp (by continuity)
    exact h_cont.measurable
  exact h_outer.comp h_T

/-- Coordinates of the random `η` are jointly independent (under `apssvEtaMeasure`). -/
@[category API, AMS 11]
lemma apssv_eta_iIndepFun :
    ProbabilityTheory.iIndepFun (fun (u : List Bool) (η : List Bool → Bool) => η u)
      apssvEtaMeasure := by
  unfold apssvEtaMeasure
  exact ProbabilityTheory.iIndepFun_infinitePi (fun u => measurable_id)

/-- **Independence of the short and long σ-algebras** under `apssvEtaMeasure`: by the
joint independence of the η-coords (`apssv_eta_iIndepFun`), partitioning indices into
length-`< r` (short) and length-`≥ r` (long) yields independent `iSup`s
(`indep_iSup_of_disjoint`).

This is the structural input to the conditional independence of (Y_w)_w from σ_short
in the conditional sub-Gaussian MGF chassis: c_w (σ_short-measurable) is independent
of Y_w (σ_long-measurable). -/
@[category API, AMS 11]
lemma apssv_short_long_indep (r : ℕ) :
    ProbabilityTheory.Indep (apssvShortSigma r) (apssvLongSigma r) apssvEtaMeasure := by
  have h_eta_iIndep := apssv_eta_iIndepFun.iIndep
  set m : List Bool → MeasurableSpace (List Bool → Bool) := fun u =>
    MeasurableSpace.comap (fun η : List Bool → Bool => η u)
      (inferInstance : MeasurableSpace Bool) with hm_def
  have h_le : ∀ u : List Bool, m u ≤ (inferInstance : MeasurableSpace (List Bool → Bool)) :=
    fun u => (apssv_eta_coord_measurable u).comap_le
  have hST : Disjoint {u : List Bool | u.length < r} {u : List Bool | r ≤ u.length} := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext u
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    omega
  have h_indep_sup :=
    ProbabilityTheory.indep_iSup_of_disjoint h_le h_eta_iIndep hST
  have h_short_eq : apssvShortSigma r =
      ⨆ u ∈ {u : List Bool | u.length < r}, m u := by
    unfold apssvShortSigma
    rw [iSup_subtype]; rfl
  have h_long_eq : apssvLongSigma r =
      ⨆ u ∈ {u : List Bool | r ≤ u.length}, m u := by
    unfold apssvLongSigma
    rw [iSup_subtype]; rfl
  rw [h_short_eq, h_long_eq]
  exact h_indep_sup

/-- **`c_w` and `Y_w` are independent random variables** (per-`w`): direct corollary
of `apssv_short_long_indep` via the σ-algebra-level monotonicity. Since `c_w`
factors through `apssvShortSigma r` and `Y_w` factors through `apssvLongSigma r`,
the comap σ-algebras of `c_w`, `Y_w` are dominated by their respective short/long
σ-algebras, and `Indep`-monotonicity collapses to `IndepFun`. -/
@[category API, AMS 11]
lemma apssv_c_Y_indepFun {r : ℕ} (P k : ℕ) (w : Fin r → Bool) :
    ProbabilityTheory.IndepFun
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
      apssvEtaMeasure := by
  rw [ProbabilityTheory.IndepFun_iff_Indep]
  have h_short_long := apssv_short_long_indep r
  have h_c_le : MeasurableSpace.comap
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
      (inferInstance : MeasurableSpace ℂ) ≤ apssvShortSigma r :=
    (apssvBlockSum_c_apssvShortSigma_measurable r w k).comap_le
  have h_Y_le : MeasurableSpace.comap
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
      (inferInstance : MeasurableSpace ℂ) ≤ apssvLongSigma r :=
    (apssvBlockSum_Y_apssvLongSigma_measurable w P k).comap_le
  exact ProbabilityTheory.indep_of_indep_of_le_right
    (ProbabilityTheory.indep_of_indep_of_le_left h_short_long h_c_le) h_Y_le

/-- **iIndepFun on the paired coordinate family**: for `w ≠ w'`, the family
`(b, ℓ) ↦ η (apssvT_pairIndex w w' P (b, ℓ))` is jointly independent under
`apssvEtaMeasure`. Direct application of `apssv_eta_iIndepFun.precomp` along
`apssvT_pairIndex_injective`.

This is the iIndepFun resource feeding the eventual `IndepFun (T η w P) (T η w' P)`
claim: projecting the iIndepFun family onto the `b = false` and `b = true`
slices yields independent random sequences in `(ℕ → Bool)`, which after
composing with `apssvT_factored P` yield independent real-valued random
variables. -/
@[category API, AMS 11]
lemma apssvT_pairIndex_iIndepFun {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w') (P : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (i : Bool × ℕ) (η : List Bool → Bool) => η (apssvT_pairIndex w w' P i))
      apssvEtaMeasure :=
  apssv_eta_iIndepFun.precomp (apssvT_pairIndex_injective w w' hww' P)

/-- `apssvT η w P` is measurable in `η`. Combines `apssvT_eq_factored`
(`apssvT η w P = apssvT_factored P (η ∘ φ_w)`) with `apssvT_factored_measurable`
and the measurability of the projection `η ↦ η ∘ φ_w`. -/
@[category API, AMS 11]
lemma apssvT_measurable {r : ℕ} (w : Fin r → Bool) (P : ℕ) :
    Measurable (fun η : List Bool → Bool => apssvT η w P) := by
  -- η ↦ apssvT η w P = apssvT_factored P ∘ (η ↦ ℓ ↦ η (apssvWordPrefix w r ++ apssvPrefix P ℓ)).
  have h_eq : (fun η : List Bool → Bool => apssvT η w P) =
      apssvT_factored P ∘
        fun η : List Bool → Bool => fun ℓ => η (apssvWordPrefix w r ++ apssvPrefix P ℓ) := by
    funext η
    exact apssvT_eq_factored η w P
  rw [h_eq]
  apply (apssvT_factored_measurable P).comp
  apply measurable_pi_lambda
  intro ℓ
  exact apssv_eta_coord_measurable _

/-- Each coordinate `η ↦ η u` has the Bernoulli(1/2) law under `apssvEtaMeasure`. -/
@[category API, AMS 11]
lemma apssv_eta_coord_law (u : List Bool) :
    apssvEtaMeasure.map (fun η => η u) = apssvBoolMeasure := by
  unfold apssvEtaMeasure
  rw [MeasureTheory.Measure.infinitePi_map_eval]

/-- **Joint pushforward of the paired projection** to `(Bool × ℕ → Bool)`: under
`apssvEtaMeasure`, the joint distribution of `(b, ℓ) ↦ η (apssvT_pairIndex w w' P (b, ℓ))`
is the infinite product Bernoulli measure on `Bool × ℕ → Bool`. -/
@[category API, AMS 11]
lemma apssvT_pairIndex_pushforward {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w') (P : ℕ) :
    apssvEtaMeasure.map
        (fun η : List Bool → Bool => fun i : Bool × ℕ => η (apssvT_pairIndex w w' P i)) =
      MeasureTheory.Measure.infinitePi (fun _ : Bool × ℕ => apssvBoolMeasure) := by
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
        (fun _ => apssv_eta_coord_measurable _)).mp
      (apssvT_pairIndex_iIndepFun w w' hww' P)]
  congr 1; funext i
  exact apssv_eta_coord_law _

/-- **Single-row pushforward** (for fixed `b : Bool`): the marginal of the projection
`η ↦ ℓ ↦ η (apssvT_pairIndex w w' P (b, ℓ))` is the infinite product Bernoulli measure
on `ℕ → Bool`. Both rows (`b = false` and `b = true`) have the same marginal — what
makes them independent is their joint pushforward (see `apssvT_pairIndex_pushforward`),
not their separate marginals. -/
@[category API, AMS 11]
lemma apssvT_pairIndex_row_pushforward {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w')
    (P : ℕ) (b : Bool) :
    apssvEtaMeasure.map
        (fun η : List Bool → Bool => fun ℓ : ℕ => η (apssvT_pairIndex w w' P (b, ℓ))) =
      MeasureTheory.Measure.infinitePi (fun _ : ℕ => apssvBoolMeasure) := by
  have h_inj : Function.Injective (fun ℓ : ℕ => apssvT_pairIndex w w' P (b, ℓ)) := by
    intro ℓ₁ ℓ₂ h
    have := apssvT_pairIndex_injective w w' hww' P h
    simpa using (Prod.mk.inj this).2
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
        (fun _ => apssv_eta_coord_measurable _)).mp
      (apssv_eta_iIndepFun.precomp h_inj)]
  congr 1; funext ℓ
  exact apssv_eta_coord_law _

/-- **Curry of the pair-indexed iIndepFun**: lifting the iIndepFun on `Bool × ℕ`
to a `Bool`-indexed iIndepFun where each entry is the bundled `(ℕ → Bool)` projection.

Combines the joint pushforward (`apssvT_pairIndex_pushforward`) with
`MeasureTheory.Measure.infinitePi_map_curry` to identify the joint distribution,
and the row pushforward (`apssvT_pairIndex_row_pushforward`) for each marginal,
through `iIndepFun_iff_map_fun_eq_infinitePi_map`. -/
@[category API, AMS 11]
lemma apssvT_pairIndex_curry_iIndepFun {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w')
    (P : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (b : Bool) (η : List Bool → Bool) =>
        fun ℓ : ℕ => η (apssvT_pairIndex w w' P (b, ℓ)))
      apssvEtaMeasure := by
  have h_meas : ∀ b : Bool, Measurable (fun η : List Bool → Bool =>
      fun ℓ : ℕ => η (apssvT_pairIndex w w' P (b, ℓ))) := fun b =>
    measurable_pi_lambda _ (fun _ => apssv_eta_coord_measurable _)
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map h_meas]
  -- Identify the joint LHS via curry-from-pair pushforward.
  have h_factor : (fun η : List Bool → Bool =>
      fun b : Bool => fun ℓ : ℕ => η (apssvT_pairIndex w w' P (b, ℓ))) =
    (MeasurableEquiv.curry Bool ℕ Bool) ∘
      (fun η : List Bool → Bool => fun i : Bool × ℕ => η (apssvT_pairIndex w w' P i)) := by
    funext η b ℓ; rfl
  rw [h_factor, ← MeasureTheory.Measure.map_map (MeasurableEquiv.curry Bool ℕ Bool).measurable
        (measurable_pi_lambda _ (fun _ => apssv_eta_coord_measurable _)),
      apssvT_pairIndex_pushforward w w' hww' P]
  rw [show (fun _ : Bool × ℕ => apssvBoolMeasure) =
      (fun p : Bool × ℕ => (fun (_ : Bool) (_ : ℕ) => apssvBoolMeasure) p.1 p.2) from rfl]
  rw [MeasureTheory.Measure.infinitePi_map_curry
      (fun (_ : Bool) (_ : ℕ) => apssvBoolMeasure)]
  -- Each row's marginal is infinitePi over ℕ.
  congr 1; funext b
  exact (apssvT_pairIndex_row_pushforward w w' hww' P b).symm

@[category API, AMS 11]
lemma apssvT_indepFun_of_ne {r : ℕ} (w w' : Fin r → Bool) (hww' : w ≠ w') (P : ℕ) :
    ProbabilityTheory.IndepFun
      (fun η : List Bool → Bool => apssvT η w P)
      (fun η : List Bool → Bool => apssvT η w' P)
      apssvEtaMeasure := by
  -- Step 1: get IndepFun on the (ℕ → Bool)-projections via iIndepFun.indepFun
  --         applied to apssvT_pairIndex_curry_iIndepFun with false ≠ true.
  have h_proj_indep := (apssvT_pairIndex_curry_iIndepFun w w' hww' P).indepFun
    (i := false) (j := true) (by decide)
  -- Step 2: the two apssvT values are (apssvT_factored P) composed with each projection.
  -- Use IndepFun.comp to lift through the measurable apssvT_factored P.
  have h_apssvT_eq : ∀ (v : Fin r → Bool) (b : Bool) (η : List Bool → Bool),
      v = (if b then w' else w) →
      apssvT η v P = apssvT_factored P
        (fun ℓ : ℕ => η (apssvT_pairIndex w w' P (b, ℓ))) := by
    intro v b η hv
    rw [hv, apssvT_eq_factored]
    congr 1
  -- Apply the apssvT_factored composition.
  have h_indep_comp := h_proj_indep.comp (apssvT_factored_measurable P)
    (apssvT_factored_measurable P)
  -- Rewrite each side back to apssvT η _ P.
  have hL : (fun η : List Bool → Bool => apssvT η w P) =
      (fun η : List Bool → Bool => apssvT_factored P
        (fun ℓ => η (apssvT_pairIndex w w' P (false, ℓ)))) := by
    funext η; exact h_apssvT_eq w false η rfl
  have hR : (fun η : List Bool → Bool => apssvT η w' P) =
      (fun η : List Bool → Bool => apssvT_factored P
        (fun ℓ => η (apssvT_pairIndex w w' P (true, ℓ)))) := by
    funext η; exact h_apssvT_eq w' true η rfl
  rw [hL, hR]
  exact h_indep_comp

/- ## Full iIndepFun extension across all `w : Fin r → Bool` (Step 3 prep)

The pairwise machinery (`apssvT_pairIndex_*`) handled two `w, w'` at a time.
For Hoeffding's inequality on `B = ∑_w Z_w`, we need the full iIndepFun across
the entire family `(Y_w := e(k T_{w, P}/2^r))_{w : Fin r → Bool}`. The pattern
mirrors the pairwise version but with `(Fin r → Bool) × ℕ` indexing instead of
`Bool × ℕ`. -/

/-- **Joint partition index**: `(w, ℓ) ↦ apssvWordPrefix w r ++ apssvPrefix P ℓ`,
mapping the index space `(Fin r → Bool) × ℕ` into `List Bool`. Generalizes
`apssvT_pairIndex` (which handled only `Bool` for the `w`-coordinate). -/
@[category API, AMS 11]
def apssvT_partIndex (r P : ℕ) : (Fin r → Bool) × ℕ → List Bool :=
  fun ⟨w, ℓ⟩ => apssvWordPrefix w r ++ apssvPrefix P ℓ

/-- The joint partition index is injective: distinct `(w, ℓ)` produce distinct
lists. Length forces equal `ℓ`; then the first `r` entries identify `w`. -/
@[category API, AMS 11]
lemma apssvT_partIndex_injective (r P : ℕ) :
    Function.Injective (apssvT_partIndex r P) := by
  rintro ⟨w₁, ℓ₁⟩ ⟨w₂, ℓ₂⟩ h
  -- Unfold to the underlying append form.
  have h' : apssvWordPrefix w₁ r ++ apssvPrefix P ℓ₁ =
            apssvWordPrefix w₂ r ++ apssvPrefix P ℓ₂ := h
  -- Length: r + ℓ₁ = r + ℓ₂ ⟹ ℓ₁ = ℓ₂.
  have h_len : (apssvWordPrefix w₁ r ++ apssvPrefix P ℓ₁).length =
      (apssvWordPrefix w₂ r ++ apssvPrefix P ℓ₂).length := congr_arg _ h'
  rw [List.length_append, List.length_append, apssvWordPrefix_length,
      apssvWordPrefix_length, apssvPrefix_length, apssvPrefix_length] at h_len
  have h_ℓ : ℓ₁ = ℓ₂ := by omega
  subst h_ℓ
  -- Take first r elements: apssvWordPrefix w₁ r = apssvWordPrefix w₂ r ⟹ w₁ = w₂.
  have h_take : apssvWordPrefix w₁ r = apssvWordPrefix w₂ r := by
    have := congr_arg (List.take r) h'
    rwa [List.take_left' (apssvWordPrefix_length _ r),
         List.take_left' (apssvWordPrefix_length _ r)] at this
  exact Prod.mk.injEq .. |>.mpr ⟨apssvWordPrefix_injective h_take, rfl⟩

/-- **Joint iIndepFun on `(Fin r → Bool) × ℕ`**: precomposing
`apssv_eta_iIndepFun` with the injective `apssvT_partIndex r P`. -/
@[category API, AMS 11]
lemma apssvT_partIndex_iIndepFun (r P : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (i : (Fin r → Bool) × ℕ) (η : List Bool → Bool) =>
        η (apssvT_partIndex r P i))
      apssvEtaMeasure :=
  apssv_eta_iIndepFun.precomp (apssvT_partIndex_injective r P)

/-- **Joint pushforward on `(Fin r → Bool) × ℕ`**: under `apssvEtaMeasure`,
`(η ↦ i ↦ η (apssvT_partIndex r P i))` has pushforward equal to
`infinitePi (Bernoulli)` on `((Fin r → Bool) × ℕ → Bool)`. -/
@[category API, AMS 11]
lemma apssvT_partIndex_pushforward (r P : ℕ) :
    apssvEtaMeasure.map
        (fun η : List Bool → Bool => fun i : (Fin r → Bool) × ℕ =>
          η (apssvT_partIndex r P i)) =
      MeasureTheory.Measure.infinitePi
        (fun _ : (Fin r → Bool) × ℕ => apssvBoolMeasure) := by
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
        (fun _ => apssv_eta_coord_measurable _)).mp
      (apssvT_partIndex_iIndepFun r P)]
  congr 1; funext i
  exact apssv_eta_coord_law _

/-- **Single-row pushforward (any `w`)**: the marginal of
`η ↦ ℓ ↦ η (apssvT_partIndex r P (w, ℓ))` is the infinite product Bernoulli
measure on `ℕ → Bool`. -/
@[category API, AMS 11]
lemma apssvT_partIndex_row_pushforward (r P : ℕ) (w : Fin r → Bool) :
    apssvEtaMeasure.map
        (fun η : List Bool → Bool => fun ℓ : ℕ => η (apssvT_partIndex r P (w, ℓ))) =
      MeasureTheory.Measure.infinitePi (fun _ : ℕ => apssvBoolMeasure) := by
  have h_inj : Function.Injective (fun ℓ : ℕ => apssvT_partIndex r P (w, ℓ)) := by
    intro ℓ₁ ℓ₂ h
    have := apssvT_partIndex_injective r P h
    simpa using (Prod.mk.inj this).2
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
        (fun _ => apssv_eta_coord_measurable _)).mp
      (apssv_eta_iIndepFun.precomp h_inj)]
  congr 1; funext ℓ
  exact apssv_eta_coord_law _

/-- **Curry of the joint iIndepFun**: lifting the `(Fin r → Bool) × ℕ`-iIndepFun
to a `(Fin r → Bool)`-indexed iIndepFun where each entry is the bundled
`(ℕ → Bool)` projection. Mirrors `apssvT_pairIndex_curry_iIndepFun` for the
full family. -/
@[category API, AMS 11]
lemma apssvT_partIndex_curry_iIndepFun (r P : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (w : Fin r → Bool) (η : List Bool → Bool) =>
        fun ℓ : ℕ => η (apssvT_partIndex r P (w, ℓ)))
      apssvEtaMeasure := by
  have h_meas : ∀ w : Fin r → Bool, Measurable (fun η : List Bool → Bool =>
      fun ℓ : ℕ => η (apssvT_partIndex r P (w, ℓ))) := fun w =>
    measurable_pi_lambda _ (fun _ => apssv_eta_coord_measurable _)
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map h_meas]
  -- Identify the joint LHS via curry-from-pair pushforward.
  have h_factor : (fun η : List Bool → Bool =>
      fun w : Fin r → Bool => fun ℓ : ℕ => η (apssvT_partIndex r P (w, ℓ))) =
    (MeasurableEquiv.curry (Fin r → Bool) ℕ Bool) ∘
      (fun η : List Bool → Bool => fun i : (Fin r → Bool) × ℕ =>
        η (apssvT_partIndex r P i)) := by
    funext η w ℓ; rfl
  rw [h_factor, ← MeasureTheory.Measure.map_map
        (MeasurableEquiv.curry (Fin r → Bool) ℕ Bool).measurable
        (measurable_pi_lambda _ (fun _ => apssv_eta_coord_measurable _)),
      apssvT_partIndex_pushforward r P]
  rw [show (fun _ : (Fin r → Bool) × ℕ => apssvBoolMeasure) =
      (fun p : (Fin r → Bool) × ℕ =>
        (fun (_ : Fin r → Bool) (_ : ℕ) => apssvBoolMeasure) p.1 p.2) from rfl]
  rw [MeasureTheory.Measure.infinitePi_map_curry
      (fun (_ : Fin r → Bool) (_ : ℕ) => apssvBoolMeasure)]
  congr 1; funext w
  exact (apssvT_partIndex_row_pushforward r P w).symm

/-- **Full iIndepFun of the `apssvT` family across `w`**: under `apssvEtaMeasure`,
the family `(η ↦ apssvT η w P)_{w : Fin r → Bool}` is jointly independent.

Proof: each `apssvT η w P = apssvT_factored P (η ∘ apssvT_partIndex r P (w, ·))` is
the composition of the (measurable) deterministic function `apssvT_factored P`
with the row projection `η ↦ ℓ ↦ η (apssvT_partIndex r P (w, ℓ))`. The rows are
iIndepFun (by `apssvT_partIndex_curry_iIndepFun`); composing with `apssvT_factored P`
preserves iIndepFun (`iIndepFun.comp`).

**Use**: feeds Hoeffding's inequality applied to `B = ∑_w Z_w` (Step 4 of
the APSSV proof), where `Z_w := c_w · (e(k T_{w, P}/2^r) - α)` with `c_w`
F_{<r}-measurable and `Y_w := e(k T_{w, P}/2^r)` long-coord-measurable. -/
@[category API, AMS 11]
lemma apssvT_iIndepFun (r P : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (w : Fin r → Bool) (η : List Bool → Bool) => apssvT η w P)
      apssvEtaMeasure := by
  -- Each apssvT η w P factors as apssvT_factored P composed with the row projection.
  have h_eq : (fun (w : Fin r → Bool) (η : List Bool → Bool) => apssvT η w P) =
      fun (w : Fin r → Bool) (η : List Bool → Bool) =>
        apssvT_factored P (fun ℓ : ℕ => η (apssvT_partIndex r P (w, ℓ))) := by
    funext w η
    exact apssvT_eq_factored η w P
  rw [h_eq]
  exact (apssvT_partIndex_curry_iIndepFun r P).comp
    (fun _ : Fin r → Bool => apssvT_factored P)
    (fun _ => apssvT_factored_measurable P)

/-- **iIndepFun of the Fourier weights `Y_w := e(k T_{w, P}/2^r)` across `w`**:
direct corollary of `apssvT_iIndepFun` via composition with the (measurable)
deterministic map `t ↦ e(k·t/2^r)`. -/
@[category API, AMS 11]
lemma apssvT_e_iIndepFun (P r k : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (w : Fin r → Bool) (η : List Bool → Bool) =>
        e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
      apssvEtaMeasure := by
  -- Each Y_w = (t ↦ e(k·t/2^r)) ∘ (η ↦ apssvT η w P).
  have h_continuous : Continuous (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) := by
    unfold e; refine Complex.continuous_exp.comp ?_; continuity
  have h_meas : ∀ _ : Fin r → Bool, Measurable (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) :=
    fun _ => h_continuous.measurable
  exact (apssvT_iIndepFun r P).comp
    (fun _ : Fin r → Bool => fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) h_meas

/- ## Fourier weights `e(k T_{w, P}/2^r)`: integrability, expectation, w-invariance

Foundations for the variance bound and centered decomposition: the Fourier
weights `e(k T_{w, P}/2^r)` are integrable, have norm-bounded expectation, and
the expectation is independent of `w` (Mathlib's `infinitePi` of i.i.d.
Bernoullis is invariant under coordinate permutation). -/

/-- The integrand `η ↦ e(k · apssvT η w P / 2^r)` is integrable on `apssvEtaMeasure`
(bounded by 1 on a probability space). -/
@[category API, AMS 11]
lemma apssvT_e_integrable {r_param : ℕ} (w : Fin r_param → Bool) (P k r : ℕ) :
    MeasureTheory.Integrable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
      apssvEtaMeasure := by
  have h_continuous_e : Continuous e := by
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  have h_meas : Measurable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := by
    apply h_continuous_e.measurable.comp
    apply (apssvT_measurable w P).const_mul _ |>.div_const
  refine MeasureTheory.Integrable.of_bound h_meas.aestronglyMeasurable 1 ?_
  apply MeasureTheory.ae_of_all
  intro η; rw [norm_e]

/-- `‖α‖ ≤ 1` where `α := ∫ e(k · apssvT η w P / 2^r) dη` is the T-factor expectation
appearing in the variance-bound calculation. Direct from `‖e(...)‖ = 1` everywhere
and `‖∫ X‖ ≤ ∫ ‖X‖` on a probability measure. -/
@[category API, AMS 11]
lemma apssvT_e_integral_norm_le_one {r_param : ℕ} (w : Fin r_param → Bool) (P k r : ℕ) :
    ‖∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖ ≤ 1 := by
  calc ‖∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖
      ≤ ∫ η, ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)‖ ∂apssvEtaMeasure :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ _ : List Bool → Bool, (1 : ℝ) ∂apssvEtaMeasure :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun η => norm_e _)
    _ = 1 := by
        rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
        exact (MeasureTheory.probReal_univ (μ := apssvEtaMeasure))

/-- **Linear-in-`k` Fourier coefficient bound** (Step 2 of [APSSV26b Prop 3.5]):
for any `w : Fin r_param → Bool`, `P k r : ℕ`,
$$ \big\|1 - \mathbb{E}\!\big[e\!\big(\tfrac{k\,T_{w, P}}{2^r}\big)\big]\big\|
   \;\le\; \frac{2 \pi k}{2^r}. $$

This is the integrated form of the pointwise Lipschitz bound
`‖e(t) - 1‖ ≤ 2π·|t|` (`e_sub_one_norm_le_abs`) applied to `t = k · T_{w, P} / 2^r`,
using `apssvT η w P ∈ [0, 1]` (via `apssvT_factored_le_one`/`apssvT_factored_nonneg`)
to bound `|t| ≤ k / 2^r`.

**Use**: combined with `apssvT_e_integral_norm_le_one` (`‖α‖ ≤ 1`), this gives
`1 - ‖α‖² ≤ 2 ‖1 - α‖ ≤ 4π·k/2^r`, hence the long-regime variance bound
`Var ≤ 4π · k`. (Stronger than the unconditional bound `Var ≤ 2 · 2^r` once
`k ≤ 2^r`.) -/
@[category API, AMS 11]
lemma apssvT_e_integral_one_sub_norm_le {r_param : ℕ} (w : Fin r_param → Bool)
    (P k r : ℕ) :
    ‖(1 : ℂ) - ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖ ≤
      2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
  -- Setup: integrand and its measurability/integrability.
  have h_continuous_e : Continuous e := by
    unfold e; exact Complex.continuous_exp.comp (by continuity)
  have h_meas : Measurable (fun η : List Bool → Bool =>
      e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := by
    refine h_continuous_e.measurable.comp ?_
    refine Measurable.div_const (Measurable.const_mul ?_ _) _
    exact apssvT_measurable w P
  have h_int : MeasureTheory.Integrable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
      apssvEtaMeasure := by
    refine MeasureTheory.Integrable.of_bound h_meas.aestronglyMeasurable 1 ?_
    refine MeasureTheory.ae_of_all _ fun η => ?_
    rw [norm_e]
  -- Rewrite `1 - α = ∫ (1 - e(...))` using `1 = ∫ 1` on the probability measure.
  have h_one : (1 : ℂ) = ∫ _ : List Bool → Bool, (1 : ℂ) ∂apssvEtaMeasure := by
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  rw [h_one, ← MeasureTheory.integral_sub (MeasureTheory.integrable_const _) h_int]
  -- Pointwise bound: ‖1 - e(k T/2^r)‖ ≤ 2π · k / 2^r.
  have h_pw : ∀ η : List Bool → Bool,
      ‖(1 : ℂ) - e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)‖ ≤
        2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
    intro η
    have h_neg : (1 : ℂ) - e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) =
        -(e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1) := by ring
    rw [h_neg, norm_neg]
    -- Bound ‖e(t) - 1‖ ≤ 2π |t| then |t| ≤ k/2^r.
    have h_e_bound :=
      e_sub_one_norm_le_abs ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)
    have hT_nn : 0 ≤ apssvT η w P := apssvT_factored_nonneg P _
    have hT_le : apssvT η w P ≤ 1 := apssvT_factored_le_one P _
    have h_arg_nn : 0 ≤ (k : ℝ) * apssvT η w P / (2 : ℝ) ^ r := by positivity
    have h_arg_le : (k : ℝ) * apssvT η w P / (2 : ℝ) ^ r ≤ (k : ℝ) / (2 : ℝ) ^ r := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ r)
      calc (k : ℝ) * apssvT η w P
          ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hT_le (Nat.cast_nonneg k)
        _ = (k : ℝ) := by ring
    have h_abs_le : |(k : ℝ) * apssvT η w P / (2 : ℝ) ^ r| ≤ (k : ℝ) / (2 : ℝ) ^ r := by
      rw [abs_of_nonneg h_arg_nn]; exact h_arg_le
    calc ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1‖
        ≤ 2 * Real.pi * |(k : ℝ) * apssvT η w P / (2 : ℝ) ^ r| := h_e_bound
      _ ≤ 2 * Real.pi * ((k : ℝ) / (2 : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left h_abs_le (by positivity)
      _ = 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by ring
  -- Apply `‖∫ f‖ ≤ C` from pointwise `‖f‖ ≤ C` on a probability measure.
  have h_le := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := apssvEtaMeasure)
    (C := 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r)
    (f := fun η : List Bool → Bool => (1 : ℂ) - e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
    (MeasureTheory.ae_of_all _ h_pw)
  -- μ.real univ = 1 on a probability measure.
  rw [MeasureTheory.probReal_univ (μ := apssvEtaMeasure), mul_one] at h_le
  exact h_le

/-- **Quadratic deficit form** (corollary of `apssvT_e_integral_one_sub_norm_le`):
$$ 1 - \big\|\mathbb{E}[e(k T_{w, P} / 2^r)]\big\|^2 \;\le\; \frac{4 \pi k}{2^r}. $$

Proof: with `α := ∫ e(k T/2^r)`, `‖α‖ ≤ 1` (`apssvT_e_integral_norm_le_one`), so
`1 - ‖α‖² = (1 - ‖α‖)(1 + ‖α‖) ≤ 2(1 - ‖α‖) ≤ 2 ‖1 - α‖ ≤ 2 · (2π·k/2^r) = 4π·k/2^r`,
where the last bound is `apssvT_e_integral_one_sub_norm_le`.

**Use**: Combined with the variance identity `∫ ‖B‖² = 2^r · (1 - ‖α‖²)` (extracted
inside the proof of `apssvBlockSum_variance_bound`), this yields the linear-in-`k`
variance bound `∫ ‖B‖² ≤ 4π · k` — strictly better than `2 · 2^r` whenever
`k ≤ 2^(r - 1)/π`, i.e., in the long-regime `r ≥ b(k) + O(1)`. -/
@[category API, AMS 11]
lemma apssvT_e_integral_one_sub_norm_sq_le {r_param : ℕ} (w : Fin r_param → Bool)
    (P k r : ℕ) :
    1 - ‖∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖ ^ 2 ≤
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
  set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure with hα_def
  have h_norm_le : ‖α‖ ≤ 1 := by rw [hα_def]; exact apssvT_e_integral_norm_le_one w P k r
  have h_norm_nn : 0 ≤ ‖α‖ := norm_nonneg _
  have h_one_sub : ‖(1 : ℂ) - α‖ ≤ 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
    rw [hα_def]; exact apssvT_e_integral_one_sub_norm_le w P k r
  -- 1 - ‖α‖ ≤ ‖1 - α‖ via reverse triangle inequality.
  have h_one_sub_norm : 1 - ‖α‖ ≤ ‖(1 : ℂ) - α‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) α
    rw [norm_one] at h
    have := abs_le.mp h
    linarith [this.1, this.2]
  -- 1 - ‖α‖² = (1 - ‖α‖)(1 + ‖α‖) ≤ 2(1 - ‖α‖) ≤ 2 ‖1 - α‖.
  have h_factor : 1 - ‖α‖ ^ 2 = (1 - ‖α‖) * (1 + ‖α‖) := by ring
  have h_one_plus : 1 + ‖α‖ ≤ 2 := by linarith
  have h_one_sub_nn : 0 ≤ 1 - ‖α‖ := by linarith
  calc 1 - ‖α‖ ^ 2
      = (1 - ‖α‖) * (1 + ‖α‖) := h_factor
    _ ≤ (1 - ‖α‖) * 2 :=
        mul_le_mul_of_nonneg_left h_one_plus h_one_sub_nn
    _ = 2 * (1 - ‖α‖) := by ring
    _ ≤ 2 * ‖(1 : ℂ) - α‖ :=
        mul_le_mul_of_nonneg_left h_one_sub_norm (by norm_num)
    _ ≤ 2 * (2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h_one_sub (by norm_num)
    _ = 4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by ring

/-- **Cross-term integral factorization** for the L² expansion. Using
`apssvT_indepFun_of_ne` (the long-prefix factor is independent across `w ≠ w'`)
together with `IndepFun.integral_mul_eq_mul_integral`, the expectation of the
T-difference exponential factors:
$$ \mathbb{E}\!\left[e\!\left(\frac{k\,(T_{w,P} - T_{w',P})}{2^r}\right)\right] =
   \mathbb{E}\!\left[e\!\left(\frac{k\,T_{w,P}}{2^r}\right)\right]
   \cdot \mathbb{E}\!\left[e\!\left(-\frac{k\,T_{w',P}}{2^r}\right)\right]. $$
This is the form in which the cross-term enters the variance bound. -/
@[category API, AMS 11]
lemma apssvBlockSum_T_diff_E_factor {r_param : ℕ} (w w' : Fin r_param → Bool)
    (hww' : w ≠ w') (P k : ℕ) :
    ∫ η, e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r_param)
        ∂apssvEtaMeasure =
      (∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r_param) ∂apssvEtaMeasure) *
      (∫ η, e (-((k : ℝ) * apssvT η w' P / (2 : ℝ) ^ r_param)) ∂apssvEtaMeasure) := by
  -- Pointwise: e(k(T_w-T_w')/2^r) = e(k·T_w/2^r) · e(-k·T_w'/2^r).
  have h_point : ∀ η,
      e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r_param) =
        e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r_param) *
        e (-((k : ℝ) * apssvT η w' P / (2 : ℝ) ^ r_param)) := by
    intro η
    rw [← e_add]; congr 1; ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_point)]
  -- Build IndepFun on the two e-factors via composition.
  have h_indep := apssvT_indepFun_of_ne w w' hww' P
  have h_meas_φ : Measurable (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r_param)) := by
    apply Continuous.measurable
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  have h_meas_ψ : Measurable (fun t : ℝ => e (-((k : ℝ) * t / (2 : ℝ) ^ r_param))) := by
    apply Continuous.measurable
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  have h_indep' := h_indep.comp h_meas_φ h_meas_ψ
  -- Strong-measurability of the e-composed factors (continuous of measurable).
  have h_strong_X : MeasureTheory.AEStronglyMeasurable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r_param))
      apssvEtaMeasure :=
    (h_meas_φ.comp (apssvT_measurable w P)).aestronglyMeasurable
  have h_strong_Y : MeasureTheory.AEStronglyMeasurable
      (fun η : List Bool → Bool => e (-((k : ℝ) * apssvT η w' P / (2 : ℝ) ^ r_param)))
      apssvEtaMeasure :=
    (h_meas_ψ.comp (apssvT_measurable w' P)).aestronglyMeasurable
  -- Apply IndepFun.integral_fun_mul_eq_mul_integral.
  exact h_indep'.integral_fun_mul_eq_mul_integral h_strong_X h_strong_Y

/-- **Short-vs-long independence**: the j-factor (which depends on `η` only at
short prefixes, length `< r`) is independent of the T-factor (which depends on
`η` only at long prefixes, length `≥ r`). The two sets of η-coordinates are
disjoint by length, so independence follows from the iIndepFun structure on
`apssvEtaMeasure`.

**Proof sketch**: define a `Bool ⊕ ℕ`-style paired index `g : (Sum ?_short ℕ) →
List Bool` whose first component enumerates the (finite) short coords used by
`j(w), j(w')` and second component enumerates the (countable) long coords used
by `T(w,P), T(w',P)`. By `apssvWordPrefix` length comparison, `g` is injective.
By `apssv_eta_iIndepFun.precomp g`, we get a paired iIndepFun, and a curry step
analogous to `apssvT_pairIndex_curry_iIndepFun` lifts to a 2-element family
indexed by Bool. Then `iIndepFun.indepFun (false ≠ true)` gives `IndepFun` of
the two projections; composing with measurable `j(w), j(w'), T(w,P), T(w',P)
↦ e(...)` lifts to the j-factor and T-factor.

**Status**: closed. The proof case-splits on `w = w'` (j-factor is constant `1`,
trivial) vs `w ≠ w'` (partition the η-coordinates into `length < r` (short) and
`length ≥ r` (long), use `apssv_eta_iIndepFun.iIndep` plus
`indep_iSup_of_disjoint`, then bridge with explicit `Measurable` checks that the
j-factor is `⨆ u ∈ Short, m u`-measurable and the T-factor is `⨆ u ∈ Long, m u`-
measurable). -/
@[category API, AMS 11]
lemma apssvBlockSum_j_T_indepFun {r : ℕ} (w w' : Fin r → Bool) (P k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun η : List Bool → Bool =>
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r))
      (fun η : List Bool → Bool =>
        e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r))
      apssvEtaMeasure := by
  by_cases hww' : w = w'
  · -- w = w': j-factor reduces to e(0) = 1 (constant), so independence is trivial.
    subst hww'
    have h_const : (fun η : List Bool → Bool =>
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) / (2 : ℝ) ^ r)) =
        fun _ => 1 := by
      funext η
      rw [show ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) = 0 from by ring]
      rw [show ((k : ℝ) * 0 / (2 : ℝ) ^ r) = 0 from by ring]
      exact e_zero
    rw [h_const]
    exact ProbabilityTheory.indepFun_const_left _ _
  · -- w ≠ w': partition argument. The j-factor's σ-algebra is contained in the
    -- σ-algebra of "events depending on η at short coords" (lists of length < r),
    -- and the T-factor's σ-algebra is contained in "events depending on η at long
    -- coords" (length ≥ r). These two are disjoint, so by `indep_iSup_of_disjoint`
    -- applied to the iIndep structure on apssv_eta, the two σ-algebras are
    -- independent — hence the j-factor and T-factor are independent functions.
    -- Set up: ShortSet = lists of length < r; LongSet = lists of length ≥ r.
    set ShortSet : Set (List Bool) := {u | u.length < r} with hShort_def
    set LongSet : Set (List Bool) := {u | r ≤ u.length} with hLong_def
    have h_disj : Disjoint ShortSet LongSet := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext u
      simp [ShortSet, LongSet]
    -- The atomic σ-algebras: m u = comap of η ↦ η u, where the codomain Bool has top.
    let m : List Bool → MeasurableSpace (List Bool → Bool) :=
      fun u => MeasurableSpace.comap (fun η : List Bool → Bool => η u) Bool.instMeasurableSpace
    -- iIndep version of apssv_eta_iIndepFun on these atomic σ-algebras.
    have h_iIndep : ProbabilityTheory.iIndep m apssvEtaMeasure :=
      apssv_eta_iIndepFun.iIndep
    -- All atomic σ-algebras are ≤ the ambient measurable space.
    have h_le : ∀ u : List Bool, m u ≤
        (inferInstance : MeasurableSpace (List Bool → Bool)) := fun u =>
      (apssv_eta_coord_measurable u).comap_le
    -- Apply indep_iSup_of_disjoint to get Indep on the suprema.
    have h_indep_sup := ProbabilityTheory.indep_iSup_of_disjoint h_le h_iIndep h_disj
    -- h_indep_sup : Indep (⨆ u ∈ ShortSet, m u) (⨆ u ∈ LongSet, m u) apssvEtaMeasure
    have h_continuous_e : Continuous e := by
      unfold e; exact Complex.continuous_exp.comp (by continuity)
    have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
    -- Measurability of apssvJ wrt SHORT.
    have h_apssvJ_short : ∀ v : Fin r → Bool, @Measurable _ _
        (⨆ u ∈ ShortSet, m u) Nat.instMeasurableSpace
        (fun η : List Bool → Bool => apssvJ η r v) := by
      intro v
      unfold apssvJ
      refine Finset.measurable_sum _ fun i _ => ?_
      by_cases hi : i < r
      · simp only [hi, dite_true]
        refine Measurable.ite ?_ measurable_const measurable_const
        have h_short_mem : apssvWordPrefix v i ∈ ShortSet := by
          show (apssvWordPrefix v i).length < r
          rw [apssvWordPrefix_length]; exact hi
        have h_coord_short : @Measurable _ _
            (⨆ u ∈ ShortSet, m u) Bool.instMeasurableSpace
            (fun η : List Bool → Bool => η (apssvWordPrefix v i)) :=
          (comap_measurable (m := Bool.instMeasurableSpace) _).mono
            (le_iSup₂_of_le (apssvWordPrefix v i) h_short_mem le_rfl) le_rfl
        have h_xor_short : @Measurable _ _
            (⨆ u ∈ ShortSet, m u) Bool.instMeasurableSpace
            (fun η : List Bool → Bool => (v ⟨i, hi⟩).xor (η (apssvWordPrefix v i))) :=
          ((measurable_of_countable _ : Measurable (fun b : Bool =>
            (v ⟨i, hi⟩).xor b))).comp h_coord_short
        exact h_xor_short (measurableSet_singleton true)
      · simp only [hi, dite_false]
        exact measurable_const
    -- Show comap(j-factor) ≤ ⨆_short m u via measurability composition.
    have h_jfactor_le : MeasurableSpace.comap (fun η : List Bool → Bool =>
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r))
        Complex.measurableSpace ≤
        ⨆ u ∈ ShortSet, m u := by
      have h_meas : @Measurable _ _
          (⨆ u ∈ ShortSet, m u) Complex.measurableSpace
          (fun η : List Bool → Bool =>
            e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)) := by
        refine h_continuous_e.measurable.comp ?_
        refine Measurable.div_const (Measurable.const_mul ?_ _) _
        exact (h_natCast_real.comp (h_apssvJ_short w)).sub
              (h_natCast_real.comp (h_apssvJ_short w'))
      exact h_meas.comap_le
    -- Show comap(T-factor) ≤ ⨆_long m u.
    -- T-factor's value depends on η at apssvWordPrefix v r ++ apssvPrefix P ℓ
    -- for ℓ : ℕ, all of length ≥ r ∈ LongSet.
    have h_apssvT_long : ∀ v : Fin r → Bool, @Measurable _ _
        (⨆ u ∈ LongSet, m u) Real.measurableSpace
        (fun η : List Bool → Bool => apssvT η v P) := by
      intro v
      -- Rewrite via apssvT_eq_factored: apssvT η v P = apssvT_factored P ∘ (η ↦ ℓ ↦ η at long coord).
      have h_eq : (fun η : List Bool → Bool => apssvT η v P) =
          apssvT_factored P ∘
            (fun η : List Bool → Bool => fun ℓ : ℕ =>
              η (apssvWordPrefix v r ++ apssvPrefix P ℓ)) := by
        funext η; exact apssvT_eq_factored η v P
      rw [h_eq]
      refine (apssvT_factored_measurable P).comp ?_
      -- Show the projection (ℓ ↦ η at long coord) is ⨆_long-measurable.
      refine (@measurable_pi_iff _ _ _ (⨆ u ∈ LongSet, m u) _ _).mpr fun ℓ => ?_
      -- Each component coord η ↦ η (apssvWordPrefix v r ++ apssvPrefix P ℓ) is in m_(...) ≤ ⨆_long.
      have h_long_mem : (apssvWordPrefix v r ++ apssvPrefix P ℓ) ∈ LongSet := by
        show r ≤ (apssvWordPrefix v r ++ apssvPrefix P ℓ).length
        rw [List.length_append, apssvWordPrefix_length]
        exact Nat.le_add_right _ _
      exact (comap_measurable (m := Bool.instMeasurableSpace) _).mono
        (le_iSup₂_of_le (apssvWordPrefix v r ++ apssvPrefix P ℓ) h_long_mem le_rfl) le_rfl
    have h_Tfactor_le : MeasurableSpace.comap (fun η : List Bool → Bool =>
        e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r))
        Complex.measurableSpace ≤
        ⨆ u ∈ LongSet, m u := by
      have h_meas : @Measurable _ _
          (⨆ u ∈ LongSet, m u) Complex.measurableSpace
          (fun η : List Bool → Bool =>
            e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r)) := by
        refine h_continuous_e.measurable.comp ?_
        refine Measurable.div_const (Measurable.const_mul ?_ _) _
        exact (h_apssvT_long w).sub (h_apssvT_long w')
      exact h_meas.comap_le
    -- Convert IndepFun to Indep via IndepFun_iff_Indep, then use monotonicity.
    rw [ProbabilityTheory.IndepFun_iff_Indep]
    -- Need Indep (comap j) (comap T) apssvEtaMeasure.
    -- Use h_indep_sup + monotonicity (smaller σ-algebras inherit independence).
    rw [ProbabilityTheory.Indep_iff]
    intro t1 t2 ht1 ht2
    rw [ProbabilityTheory.Indep_iff] at h_indep_sup
    exact h_indep_sup t1 t2 (h_jfactor_le t1 ht1) (h_Tfactor_le t2 ht2)

/- ## Bit-flip symmetry: pushforward under η-coordinate flips

Tools to evaluate `∫ e(k · apssvT η w P / 2^r) dη`: a single-coordinate flip
on `η` rotates the integrand by `e^{i π · sign} = ±1`, and `apssvEtaMeasure`
is invariant under the flip — so the integral is `0` whenever a single
relevant coordinate's flip negates the integrand. -/

/-- The Bernoulli(1/2) measure assigns mass `1/2` to each singleton in `Bool`. -/
@[category API, AMS 11]
lemma apssvBoolMeasure_singleton (b : Bool) : apssvBoolMeasure {b} = 1/2 := by
  unfold apssvBoolMeasure apssvBoolPMF
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b)]
  simp [PMF.bernoulli_apply]
  cases b <;> simp

/-- The Bernoulli(1/2) measure on `Bool` is invariant under `Bool.not`. Elementary
symmetry: under `Bool.not`, `{true} ↔ {false}`, and the measure of both is `1/2`. -/
@[category API, AMS 11]
lemma apssvBoolMeasure_map_not :
    apssvBoolMeasure.map Bool.not = apssvBoolMeasure := by
  refine MeasureTheory.Measure.ext_of_singleton fun b => ?_
  rw [MeasureTheory.Measure.map_apply (measurable_of_countable _)
      (MeasurableSet.singleton _)]
  have h_pre : Bool.not ⁻¹' {b} = {!b} := by
    ext x; simp [Set.mem_preimage, Set.mem_singleton_iff]
  rw [h_pre, apssvBoolMeasure_singleton, apssvBoolMeasure_singleton]

/-- Flip the value of `η` at a single coordinate `c`, leaving every other coordinate
fixed. The key measure-preserving symmetry of `apssvEtaMeasure` (formalized in
`apssvEtaMeasure_map_flipAt`). -/
@[category API, AMS 11]
def apssvFlipAt (c : List Bool) (η : List Bool → Bool) : List Bool → Bool :=
  fun c' => if c' = c then !η c' else η c'

@[category API, AMS 11]
lemma apssvFlipAt_measurable (c : List Bool) :
    Measurable (apssvFlipAt c) := by
  rw [measurable_pi_iff]
  intro c'
  by_cases h : c' = c
  · have hf : (fun η : List Bool → Bool => apssvFlipAt c η c') = (fun η => !η c') := by
      funext η; unfold apssvFlipAt; simp [h]
    rw [hf]
    exact (measurable_of_countable Bool.not).comp (apssv_eta_coord_measurable c')
  · have hf : (fun η : List Bool → Bool => apssvFlipAt c η c') = (fun η => η c') := by
      funext η; unfold apssvFlipAt; simp [h]
    rw [hf]
    exact apssv_eta_coord_measurable c'

/-- **Key measure-preserving symmetry**: `apssvEtaMeasure` is invariant under flipping
the value of `η` at any single coordinate. Direct application of `infinitePi_map_pi`
(coordinate-wise pushforward decomposition) plus `apssvBoolMeasure_map_not` (the
single-coordinate invariance). -/
@[category API, AMS 11]
lemma apssvEtaMeasure_map_flipAt (c : List Bool) :
    apssvEtaMeasure.map (apssvFlipAt c) = apssvEtaMeasure := by
  -- Rewrite apssvFlipAt as coordinate-wise application of (Bool.not on c, id elsewhere).
  let f : List Bool → Bool → Bool := fun c' b => if c' = c then !b else b
  have h_meas_f : ∀ c', Measurable (f c') := fun c' => by
    by_cases h : c' = c
    · have : f c' = Bool.not := by funext b; simp [f, h]
      rw [this]; exact measurable_of_countable _
    · have : f c' = id := by funext b; simp [f, h]
      rw [this]; exact measurable_id
  have h_eq : apssvFlipAt c = (fun η : List Bool → Bool => fun c' => f c' (η c')) := by
    funext η c'; unfold apssvFlipAt; rfl
  have key := MeasureTheory.Measure.infinitePi_map_pi
    (μ := fun _ : List Bool => apssvBoolMeasure) (Y := fun _ : List Bool => Bool) h_meas_f
  -- key : (infinitePi (fun _ => apssvBoolMeasure)).map (fun x i => f i (x i)) =
  --       infinitePi (fun i => apssvBoolMeasure.map (f i))
  calc apssvEtaMeasure.map (apssvFlipAt c)
      = apssvEtaMeasure.map (fun η : List Bool → Bool => fun c' => f c' (η c')) := by
          rw [h_eq]
    _ = MeasureTheory.Measure.infinitePi (fun c' : List Bool => apssvBoolMeasure.map (f c')) := by
          unfold apssvEtaMeasure; exact key
    _ = MeasureTheory.Measure.infinitePi (fun _ : List Bool => apssvBoolMeasure) := by
          congr 1
          funext c'
          by_cases h : c' = c
          · have hf : f c' = Bool.not := by funext b; simp [f, h]
            rw [hf]; exact apssvBoolMeasure_map_not
          · have hf : f c' = id := by funext b; simp [f, h]
            rw [hf]; exact MeasureTheory.Measure.map_id
    _ = apssvEtaMeasure := rfl

/-- The flip-at-c map preserves `apssvEtaMeasure` as a measure-preserving function. -/
@[category API, AMS 11]
lemma apssvFlipAt_measurePreserving (c : List Bool) :
    MeasureTheory.MeasurePreserving (apssvFlipAt c) apssvEtaMeasure apssvEtaMeasure :=
  ⟨apssvFlipAt_measurable c, apssvEtaMeasure_map_flipAt c⟩

/-- **Pointwise change of `apssvT_factored` under one-coordinate flip**: flipping
the `ℓ₀`-th coordinate of `b` shifts `apssvT_factored P b` by exactly the
single-term contribution at `ℓ₀`. -/
@[category API, AMS 11]
lemma apssvT_factored_update_eq (P ℓ₀ : ℕ) (b : ℕ → Bool) :
    apssvT_factored P (Function.update b ℓ₀ (!b ℓ₀)) =
    apssvT_factored P b +
    ((1 : ℝ) - 2 * (if (P.testBit ℓ₀).xor (b ℓ₀) then (1 : ℝ) else 0)) / 2 ^ (ℓ₀ + 1) := by
  classical
  unfold apssvT_factored
  set f : ℕ → ℝ := fun ℓ : ℕ =>
    (if (P.testBit ℓ).xor (b ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1) with hf_def
  set f' : ℕ → ℝ := fun ℓ : ℕ =>
    (if (P.testBit ℓ).xor (Function.update b ℓ₀ (!b ℓ₀) ℓ) then (1 : ℝ) else 0) / 2 ^ (ℓ + 1)
    with hf'_def
  have h_summ_b : Summable f := apssvT_factored_summable P b
  have h_summ_b' : Summable f' := apssvT_factored_summable P (Function.update b ℓ₀ (!b ℓ₀))
  -- ∑' f' = f' ℓ₀ + ∑' (ite ℓ = ℓ₀ then 0 else f' ℓ); same for f.
  rw [h_summ_b'.tsum_eq_add_tsum_ite ℓ₀, h_summ_b.tsum_eq_add_tsum_ite ℓ₀]
  -- The "rest" tsums agree termwise (f and f' coincide off ℓ₀).
  have h_rest_eq :
      (∑' ℓ, if ℓ = ℓ₀ then (0 : ℝ) else f' ℓ) =
      (∑' ℓ, if ℓ = ℓ₀ then (0 : ℝ) else f ℓ) := by
    refine tsum_congr (fun ℓ => ?_)
    by_cases h : ℓ = ℓ₀
    · simp [h]
    · simp only [h, if_false, hf_def, hf'_def, Function.update_of_ne h]
  rw [h_rest_eq]
  -- Compute f' ℓ₀ - f ℓ₀ = (1 - 2·old)/2^(ℓ₀+1).
  have h_f'_ℓ₀ : f' ℓ₀ =
      (if (P.testBit ℓ₀).xor (!b ℓ₀) then (1 : ℝ) else 0) / 2 ^ (ℓ₀ + 1) := by
    show (if (P.testBit ℓ₀).xor (Function.update b ℓ₀ (!b ℓ₀) ℓ₀) then (1 : ℝ) else 0) /
        2 ^ (ℓ₀ + 1) = _
    rw [Function.update_self]
  have h_xor_flip :
      (if (P.testBit ℓ₀).xor (!b ℓ₀) then (1 : ℝ) else 0) =
      1 - (if (P.testBit ℓ₀).xor (b ℓ₀) then (1 : ℝ) else 0) := by
    have h_xor_not :
        (P.testBit ℓ₀).xor (!b ℓ₀) = !((P.testBit ℓ₀).xor (b ℓ₀)) := by
      rcases P.testBit ℓ₀ <;> rcases b ℓ₀ <;> rfl
    rw [h_xor_not]
    by_cases hxor : (P.testBit ℓ₀).xor (b ℓ₀) = true
    · rw [hxor, Bool.not_true]; simp
    · have hxf : (P.testBit ℓ₀).xor (b ℓ₀) = false := by
        rcases h : (P.testBit ℓ₀).xor (b ℓ₀) with _ | _
        · rfl
        · exact absurd h hxor
      rw [hxf, Bool.not_false]; simp
  rw [h_f'_ℓ₀, h_xor_flip]
  show (1 - (if (P.testBit ℓ₀).xor (b ℓ₀) then (1 : ℝ) else 0)) / 2 ^ (ℓ₀ + 1) +
        ∑' ℓ, (if ℓ = ℓ₀ then (0 : ℝ) else f ℓ) =
      f ℓ₀ + ∑' ℓ, (if ℓ = ℓ₀ then (0 : ℝ) else f ℓ) +
      (1 - 2 * (if (P.testBit ℓ₀).xor (b ℓ₀) then (1 : ℝ) else 0)) / 2 ^ (ℓ₀ + 1)
  simp only [hf_def]
  ring

/-- **Pointwise effect of `apssvFlipAt` on `apssvT`**: flipping `η` at the specific
coordinate `apssvWordPrefix w r ++ apssvPrefix P ℓ₀` shifts `apssvT η w P` by
exactly the single-term contribution at `ℓ₀`. Bridge from
`apssvT_factored_update_eq` via the projection to the b-sequence. -/
@[category API, AMS 11]
lemma apssvT_flipAt_eq {r : ℕ} (w : Fin r → Bool) (P ℓ₀ : ℕ) (η : List Bool → Bool) :
    apssvT (apssvFlipAt (apssvWordPrefix w r ++ apssvPrefix P ℓ₀) η) w P =
    apssvT η w P +
    ((1 : ℝ) - 2 * (if (P.testBit ℓ₀).xor
        (η (apssvWordPrefix w r ++ apssvPrefix P ℓ₀)) then (1 : ℝ) else 0)) /
      2 ^ (ℓ₀ + 1) := by
  set c : List Bool := apssvWordPrefix w r ++ apssvPrefix P ℓ₀ with hc_def
  set b : ℕ → Bool := fun ℓ => η (apssvWordPrefix w r ++ apssvPrefix P ℓ) with hb_def
  -- Step 1: the projected bit-sequence after flipping is the Function.update of b at ℓ₀.
  have h_proj_eq : (fun ℓ => apssvFlipAt c η (apssvWordPrefix w r ++ apssvPrefix P ℓ)) =
      Function.update b ℓ₀ (!b ℓ₀) := by
    funext ℓ
    by_cases hℓ : ℓ = ℓ₀
    · rw [hℓ]
      show (apssvFlipAt c η) (apssvWordPrefix w r ++ apssvPrefix P ℓ₀) =
          (Function.update b ℓ₀ (!b ℓ₀)) ℓ₀
      rw [Function.update_self]
      have h_eq_c : apssvWordPrefix w r ++ apssvPrefix P ℓ₀ = c := hc_def.symm
      rw [h_eq_c]
      unfold apssvFlipAt
      simp [hb_def, hc_def]
    · -- ℓ ≠ ℓ₀: lengths differ, so the prefix lists are unequal.
      have h_len_ne :
          (apssvWordPrefix w r ++ apssvPrefix P ℓ).length ≠ c.length := by
        simp only [hc_def, List.length_append, apssvWordPrefix_length, apssvPrefix_length]
        omega
      have h_ne : apssvWordPrefix w r ++ apssvPrefix P ℓ ≠ c := fun h_eq =>
        h_len_ne (congr_arg List.length h_eq)
      show (apssvFlipAt c η) (apssvWordPrefix w r ++ apssvPrefix P ℓ) =
          (Function.update b ℓ₀ (!b ℓ₀)) ℓ
      unfold apssvFlipAt
      simp only [if_neg h_ne, Function.update_of_ne hℓ]
      rfl
  -- Step 2: rewrite both sides via apssvT_eq_factored, then apply the update lemma.
  rw [apssvT_eq_factored, apssvT_eq_factored]
  rw [show (fun ℓ => apssvFlipAt c η (apssvWordPrefix w r ++ apssvPrefix P ℓ)) =
        Function.update b ℓ₀ (!b ℓ₀) from h_proj_eq]
  rw [apssvT_factored_update_eq]

/-- **Bit-flip multiplies `e(q · T)` by `−1`** — the key e-level identity for the
narrow-gap closure. For `q ≥ 1` and `ℓ₀ := padicValNat 2 q`, flipping `η` at the
coordinate `apssvWordPrefix w r ++ apssvPrefix P ℓ₀` shifts `q · T η w P` by an
odd half-integer, so `e` picks up `e(odd/2) = −1`. -/
@[category API, AMS 11]
lemma apssvT_e_neg_under_flip {r : ℕ} (w : Fin r → Bool) (P q : ℕ) (hq : 1 ≤ q)
    (η : List Bool → Bool) :
    e ((q : ℝ) * apssvT (apssvFlipAt
        (apssvWordPrefix w r ++ apssvPrefix P (padicValNat 2 q)) η) w P) =
    -e ((q : ℝ) * apssvT η w P) := by
  set ℓ₀ := padicValNat 2 q with hℓ₀_def
  -- Step A: factorize q = 2^ℓ₀ · q' with q' odd ≥ 1.
  have h_q_dvd : 2 ^ ℓ₀ ∣ q := pow_padicValNat_dvd
  obtain ⟨q', hq'_eq⟩ := h_q_dvd
  have h_q'_pos : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with hq'_zero | hq'_pos
    · subst hq'_zero; rw [Nat.mul_zero] at hq'_eq; omega
    · exact hq'_pos
  have hq_ne : q ≠ 0 := Nat.one_le_iff_ne_zero.mp hq
  have h_q'_odd : Odd q' := by
    by_contra h_not_odd
    rw [Nat.not_odd_iff_even] at h_not_odd
    obtain ⟨n, hn⟩ := h_not_odd
    -- q = 2^ℓ₀ · q' = 2^ℓ₀ · (n + n) = 2^(ℓ₀+1) · n.
    have h_dvd_succ : 2 ^ (ℓ₀ + 1) ∣ q := by
      rw [hq'_eq, hn, pow_succ]
      exact ⟨n, by ring⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact pow_succ_padicValNat_not_dvd (p := 2) hq_ne h_dvd_succ
  -- Step B: apply pointwise T-shift.
  have h_T_shift := apssvT_flipAt_eq w P ℓ₀ η
  set v : ℝ := (if (P.testBit ℓ₀).xor
      (η (apssvWordPrefix w r ++ apssvPrefix P ℓ₀)) then (1 : ℝ) else 0) with hv_def
  rw [show (q : ℝ) * apssvT (apssvFlipAt
        (apssvWordPrefix w r ++ apssvPrefix P ℓ₀) η) w P =
        (q : ℝ) * apssvT η w P + (q : ℝ) * (1 - 2 * v) / 2 ^ (ℓ₀ + 1) from by
    rw [h_T_shift]; ring]
  rw [e_add]
  -- Step C: compute the e-factor on the shift = -1.
  have h_q_real : (q : ℝ) = (2 : ℝ) ^ ℓ₀ * (q' : ℝ) := by exact_mod_cast hq'_eq
  have h_e_factor : e ((q : ℝ) * (1 - 2 * v) / 2 ^ (ℓ₀ + 1)) = -1 := by
    -- Reduce q/(2^(ℓ₀+1)) = q'/2 using q = 2^ℓ₀ · q'.
    rw [h_q_real]
    have h_simplify : ((2 : ℝ) ^ ℓ₀ * (q' : ℝ)) * (1 - 2 * v) / 2 ^ (ℓ₀ + 1) =
        (q' : ℝ) * (1 - 2 * v) / 2 := by
      have h2pow_ne : ((2 : ℝ) ^ ℓ₀ : ℝ) ≠ 0 := by positivity
      rw [show (2 : ℝ) ^ (ℓ₀ + 1) = (2 : ℝ) ^ ℓ₀ * 2 from by rw [pow_succ]]
      field_simp
    rw [h_simplify]
    -- Case split on v ∈ {0, 1}.
    by_cases h_cond : (P.testBit ℓ₀).xor
        (η (apssvWordPrefix w r ++ apssvPrefix P ℓ₀)) = true
    · -- v = 1.
      have hv1 : v = 1 := by simp [hv_def, h_cond]
      rw [hv1]
      rw [show ((q' : ℝ) * (1 - 2 * 1) / 2 : ℝ) = -((q' : ℝ) / 2) from by ring]
      rw [e_neg]
      have h_eq_neg_one : e ((q' : ℝ) / 2) = -1 := by
        have h := e_half_odd q' h_q'_odd
        linear_combination h
      rw [h_eq_neg_one]
      norm_num
    · -- v = 0.
      have hv0 : v = 0 := by
        rw [hv_def]; exact if_neg h_cond
      rw [hv0]
      rw [show ((q' : ℝ) * (1 - 2 * 0) / 2 : ℝ) = (q' : ℝ) / 2 from by ring]
      have h := e_half_odd q' h_q'_odd
      linear_combination h
  rw [h_e_factor]
  ring

/-- **Integral invariance under the bit-flip**: for any AEStronglyMeasurable `g`,
`∫ η, g (apssvFlipAt c η) = ∫ η, g η`. Direct consequence of measure-preservation. -/
@[category API, AMS 11]
lemma apssvEtaMeasure_integral_comp_flipAt (c : List Bool) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (List Bool → Bool) → E)
    (hg : MeasureTheory.AEStronglyMeasurable g apssvEtaMeasure) :
    ∫ η, g (apssvFlipAt c η) ∂apssvEtaMeasure =
    ∫ η, g η ∂apssvEtaMeasure := by
  rw [show (∫ η, g (apssvFlipAt c η) ∂apssvEtaMeasure) =
        ∫ η, g η ∂(apssvEtaMeasure.map (apssvFlipAt c)) from
    (MeasureTheory.integral_map (apssvFlipAt_measurable c).aemeasurable (by
      rw [apssvEtaMeasure_map_flipAt]; exact hg)).symm]
  rw [apssvEtaMeasure_map_flipAt]

/-- **Main integral identity for the narrow gap**: for `q ≥ 1`,
`∫ η, e(q · T η w P) ∂apssvEtaMeasure = 0`.

Bit-flip symmetry argument: let `α` be the integral. The map η ↦ flip-at-c(η)
preserves the measure (`apssvEtaMeasure_map_flipAt`), so `α = ∫ e(q·T(flip(η)))`.
Pointwise, `e(q·T(flip(η))) = −e(q·T(η))` (`apssvT_e_neg_under_flip`). Hence
`α = −α`, so `α = 0`. -/
@[category API, AMS 11]
lemma apssvT_e_integral_q_eq_zero {r : ℕ} (w : Fin r → Bool) (P q : ℕ) (hq : 1 ≤ q) :
    ∫ η, e ((q : ℝ) * apssvT η w P) ∂apssvEtaMeasure = 0 := by
  set α : ℂ := ∫ η, e ((q : ℝ) * apssvT η w P) ∂apssvEtaMeasure with hα_def
  -- Measurability of the integrand.
  have h_e_cont : Continuous e := by
    unfold e; exact Complex.continuous_exp.comp (by continuity)
  have h_meas : Measurable (fun η : List Bool → Bool => e ((q : ℝ) * apssvT η w P)) :=
    h_e_cont.measurable.comp ((apssvT_measurable w P).const_mul _)
  set c : List Bool :=
    apssvWordPrefix w r ++ apssvPrefix P (padicValNat 2 q) with hc_def
  -- Step 1: change of variable via apssvFlipAt c (measure-preserving).
  have h_change :
      ∫ η, e ((q : ℝ) * apssvT (apssvFlipAt c η) w P) ∂apssvEtaMeasure = α :=
    apssvEtaMeasure_integral_comp_flipAt c _ h_meas.aestronglyMeasurable
  -- Step 2: pointwise identity from apssvT_e_neg_under_flip.
  have h_pw : ∀ η,
      e ((q : ℝ) * apssvT (apssvFlipAt c η) w P) = -e ((q : ℝ) * apssvT η w P) :=
    fun η => apssvT_e_neg_under_flip w P q hq η
  -- Step 3: integral of (-) is -(integral).
  have h_step :
      ∫ η, e ((q : ℝ) * apssvT (apssvFlipAt c η) w P) ∂apssvEtaMeasure = -α := by
    rw [show (fun η => e ((q : ℝ) * apssvT (apssvFlipAt c η) w P)) =
          (fun η => -e ((q : ℝ) * apssvT η w P)) from funext h_pw]
    rw [MeasureTheory.integral_neg, ← hα_def]
  -- Combine: α = -α, so α = 0 (since ℂ has char ≠ 2).
  have h_α_eq : α = -α := h_change.symm.trans h_step
  linear_combination h_α_eq / 2

/-- A single-coordinate constraint event has probability `1/2` under `apssvEtaMeasure`. -/
@[category API, AMS 11]
lemma apssvEtaMeasure_coord_eq (u : List Bool) (b : Bool) :
    apssvEtaMeasure {η | η u = b} = 1/2 := by
  rw [show {η : List Bool → Bool | η u = b} = (fun η => η u) ⁻¹' {b} from rfl]
  rw [← MeasureTheory.Measure.map_apply (apssv_eta_coord_measurable u)
       (MeasurableSet.singleton b)]
  rw [apssv_eta_coord_law u]
  exact apssvBoolMeasure_singleton b

/-- Integration against the Bernoulli(1/2) measure on `Bool`:
$\int f\,d\mu = (f(\mathrm{false}) + f(\mathrm{true}))/2$ for any complex-valued `f`. -/
@[category API, AMS 11]
lemma integral_apssvBoolMeasure (f : Bool → ℂ) :
    ∫ b, f b ∂apssvBoolMeasure = (f false + f true) / 2 := by
  unfold apssvBoolMeasure apssvBoolPMF
  rw [PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply]
  ring

/-- Pushforward of the integral via the coordinate map: `∫ η, f(η u) dη = ∫ b, f b db`
under the Bernoulli law of the coordinate. -/
@[category API, AMS 11]
lemma integral_apssvEta_coord (u : List Bool) (f : Bool → ℂ) :
    ∫ η, f (η u) ∂apssvEtaMeasure = ∫ b, f b ∂apssvBoolMeasure := by
  rw [← MeasureTheory.integral_map (apssv_eta_coord_measurable u).aemeasurable]
  · rw [apssv_eta_coord_law]
  · -- f is integrable on apssvEtaMeasure.map (fun η => η u) = apssvBoolMeasure (a finite measure on Bool).
    rw [apssv_eta_coord_law]
    exact (Measurable.of_discrete : Measurable f).aestronglyMeasurable

/-- The expectation of `e(k · digit_i / 2^(i+1))` over the random `η` equals
`(1 + e(k / 2^(i+1)))/2`. Here `digit_i = (n.testBit i) XOR η(apssvPrefix n i)` is
a function of `η` only through the single coordinate `η(apssvPrefix n i)` (Bernoulli 1/2).
The Bernoulli sum: $(e(k\cdot\mathrm{testBit}/2^{i+1}) + e(k\cdot(1-\mathrm{testBit})/2^{i+1}))/2
= (1 + e(k/2^{i+1}))/2$ regardless of the testBit value. -/
@[category API, AMS 11]
lemma apssv_eta_at_coord_summand_integral (P k i : ℕ) (u : List Bool) :
    ∫ η, e ((k : ℝ) *
      (if (P.testBit i).xor (η u) then (1 : ℝ) else 0) / 2 ^ (i + 1))
        ∂apssvEtaMeasure = (1 + e ((k : ℝ) / 2 ^ (i + 1))) / 2 := by
  set f : Bool → ℂ := fun b =>
    e ((k : ℝ) * (if (P.testBit i).xor b then (1 : ℝ) else 0) / 2 ^ (i + 1)) with hf_def
  show ∫ η, f (η u) ∂apssvEtaMeasure = _
  rw [integral_apssvEta_coord, integral_apssvBoolMeasure]
  rw [hf_def]
  have h_e0 : e ((k : ℝ) * 0 / 2 ^ (i + 1)) = 1 := by
    rw [show ((k : ℝ) * 0 / 2 ^ (i + 1)) = 0 from by ring]; exact e_zero
  have h_e1 : e ((k : ℝ) * 1 / 2 ^ (i + 1)) = e ((k : ℝ) / 2 ^ (i + 1)) := by
    congr 1; ring
  rcases h_tb : P.testBit i
  · show (e ((k : ℝ) * (if (false ^^ false : Bool) = true then (1:ℝ) else 0) / 2 ^ (i + 1)) +
          e ((k : ℝ) * (if (false ^^ true : Bool) = true then (1:ℝ) else 0) / 2 ^ (i + 1))) / 2 = _
    have hxorff : (false ^^ false : Bool) = false := rfl
    have hxorft : (false ^^ true : Bool) = true := rfl
    rw [hxorff, hxorft]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_e0, h_e1]
  · show (e ((k : ℝ) * (if (true ^^ false : Bool) = true then (1:ℝ) else 0) / 2 ^ (i + 1)) +
          e ((k : ℝ) * (if (true ^^ true : Bool) = true then (1:ℝ) else 0) / 2 ^ (i + 1))) / 2 = _
    have hxortf : (true ^^ false : Bool) = true := rfl
    have hxortt : (true ^^ true : Bool) = false := rfl
    rw [hxortf, hxortt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_e1, h_e0]; ring

@[category API, AMS 11]
lemma apssv_digit_summand_integral (n i k : ℕ) :
    ∫ η, e ((k : ℝ) *
      (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1))
        ∂apssvEtaMeasure = (1 + e ((k : ℝ) / 2 ^ (i + 1))) / 2 :=
  apssv_eta_at_coord_summand_integral n k i (apssvPrefix n i)

/-- Each summand of `apssvX η n` is measurable in `η`. The function factors as
`η ↦ η(apssvPrefix n i) ↦ if-then-else`; `Bool` is finite so any `Bool → ℝ` is measurable. -/
@[category API, AMS 11]
lemma apssvX_summand_measurable (n i : ℕ) :
    Measurable (fun η : List Bool → Bool =>
      (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)) := by
  apply Measurable.div_const
  have h_real_of_bool : Measurable (fun b : Bool =>
      if (n.testBit i).xor b then (1 : ℝ) else 0) := Measurable.of_discrete
  exact h_real_of_bool.comp (apssv_eta_coord_measurable _)

/-- `apssvX η n` is measurable in `η`. Lifted via `ENNReal.ofReal` to use
`Measurable.ennreal_tsum`, then `ENNReal.toReal`. -/
@[category API, AMS 11]
lemma apssvX_measurable (n : ℕ) :
    Measurable (fun η : List Bool → Bool => apssvX η n) := by
  have h_eq : (fun η : List Bool → Bool => apssvX η n) =
      fun η => (∑' i, ENNReal.ofReal
        ((if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) /
          2 ^ (i + 1))).toReal := by
    funext η
    rw [show apssvX η n = ∑' i, (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) /
        2 ^ (i + 1) from rfl]
    rw [← ENNReal.ofReal_tsum_of_nonneg (apssvX_summand_nonneg η n) (apssvX_summable η n)]
    rw [ENNReal.toReal_ofReal (tsum_nonneg (apssvX_summand_nonneg η n))]
  rw [h_eq]
  apply Measurable.ennreal_toReal
  exact Measurable.ennreal_tsum
    (fun i => ENNReal.measurable_ofReal.comp (apssvX_summand_measurable n i))

/-- `apssvBlockSum η P r k` is measurable in `η`. Uses the partial-sum form from
`apssv_block_sum_eq` (a finite sum of `e ∘ (k *) ∘ apssvX η`, each term measurable). -/
@[category API, AMS 11]
lemma apssvBlockSum_measurable (P r k : ℕ) :
    Measurable (fun η : List Bool → Bool => apssvBlockSum η P r k) := by
  -- Use the equivalent finite-sum form.
  have h_eq : (fun η : List Bool → Bool => apssvBlockSum η P r k) =
      fun η => ∑ m ∈ Finset.range (2 ^ r), e ((k : ℝ) * apssvX η (P * 2 ^ r + m)) := by
    funext η
    exact (apssv_block_sum_eq η P r k).symm
  rw [h_eq]
  apply Finset.measurable_sum _ (fun m _ => ?_)
  -- e ∘ (k *) ∘ apssvX η _ is measurable.
  have h_continuous_e : Continuous e := by
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  have h_inner : Measurable (fun η : List Bool → Bool =>
      (k : ℝ) * apssvX η (P * 2 ^ r + m)) := (apssvX_measurable _).const_mul _
  exact h_continuous_e.measurable.comp h_inner

/-- Trivial deterministic bound: `|apssvBlockSum η P r k| ≤ 2^r`. The sum has `2^r`
unit-modulus terms, so the triangle inequality gives `2^r`. This bound is the right
order for the *short-block* regime `r ≤ b/2`; the APSSV concentration argument
improves it to `√(r+b)·2^(r/2)` (a `√(r+b)/2^(r/2)` improvement) for random `η`. -/
@[category API, AMS 11]
lemma apssvBlockSum_norm_le_two_pow (η : List Bool → Bool) (P r k : ℕ) :
    ‖apssvBlockSum η P r k‖ ≤ (2 : ℝ) ^ r := by
  unfold apssvBlockSum
  refine le_trans (norm_sum_le _ _) ?_
  rw [show ((2 : ℝ) ^ r) = ∑ _w : (Fin r → Bool), (1 : ℝ) by
    rw [Finset.sum_const, Finset.card_univ]
    simp ]
  exact Finset.sum_le_sum fun w _ => by simp [norm_e]

/-- **Deterministic L² expansion identity** for `apssvBlockSum`. Setting
$f_w(\eta) := e(k \cdot (j_r(w) + T_{w, P})/2^r)$, we have:
$$ \|B_{P, r}(k)\|^2 = \sum_{w, w'} f_w(\eta) \cdot \overline{f_{w'}(\eta)}
   = \sum_{w, w'} e\!\left(\frac{k \cdot (j_r(w) - j_r(w') + T_{w,P} - T_{w',P})}{2^r}\right). $$

This is purely algebraic (no probability): expanding $\|B\|^2 = B \cdot \overline{B}$
and using `conj_e θ : conj(e θ) = (e θ)⁻¹` together with `e_neg θ : e(-θ) = (e θ)⁻¹`
to absorb the conjugation into a sign flip in the argument. The identity is the
starting point for the variance-bound calculation. -/
@[category API, AMS 11]
lemma apssvBlockSum_norm_sq_eq (η : List Bool → Bool) (P r k : ℕ) :
    ((‖apssvBlockSum η P r k‖ ^ 2 : ℝ) : ℂ) =
      ∑ w : (Fin r → Bool), ∑ w' : (Fin r → Bool),
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ) +
              apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) := by
  set B := apssvBlockSum η P r k with hB_def
  -- ‖B‖² (as ℂ) = B · conj(B).
  have h_step : ((‖B‖ ^ 2 : ℝ) : ℂ) = B * (starRingEnd ℂ) B := by
    rw [show ((‖B‖ ^ 2 : ℝ) : ℂ) = (‖B‖ : ℂ) ^ 2 from by push_cast; ring]
    have := (Complex.mul_conj B).symm
    rw [Complex.normSq_eq_norm_sq] at this
    push_cast at this
    exact this
  rw [h_step]
  -- Expand B as a sum and conj(B) as a sum.
  rw [hB_def]
  unfold apssvBlockSum
  rw [map_sum]
  -- Distribute: (∑_w f_w) · (∑_{w'} conj f_{w'}) = ∑_w ∑_{w'} f_w · conj f_{w'}.
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  -- Single term: f_w · conj f_{w'} = e(...) · e(-...) = e(... - ...).
  rw [conj_e]
  rw [show (e ((k : ℝ) * ((apssvJ η r w' : ℝ) + apssvT η w' P) / (2 : ℝ) ^ r))⁻¹ =
      e (-((k : ℝ) * ((apssvJ η r w' : ℝ) + apssvT η w' P) / (2 : ℝ) ^ r)) from by
    rw [← e_neg]]
  rw [← e_add]
  congr 1; ring

/-- **Sum of squared norms of block summands**: each $f_w$ has $|f_w| = 1$, so
the diagonal $w = w'$ contribution to the L² expansion is exactly $2^r$.

This is the "easy half" of the variance computation: the diagonal terms are
deterministic, the cross terms ($w \ne w'$) carry the probabilistic content. -/
@[category API, AMS 11]
lemma apssvBlockSum_diagonal_sum (η : List Bool → Bool) (P r k : ℕ) :
    ∑ w : (Fin r → Bool),
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ) +
            apssvT η w P - apssvT η w P) / (2 : ℝ) ^ r) = (2 : ℂ) ^ r := by
  have h_each : ∀ w : (Fin r → Bool),
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ) +
            apssvT η w P - apssvT η w P) / (2 : ℝ) ^ r) = 1 := by
    intro w
    rw [show ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ) +
              apssvT η w P - apssvT η w P) = 0 from by ring]
    rw [show ((k : ℝ) * 0 / (2 : ℝ) ^ r) = 0 from by ring]
    exact e_zero
  rw [Finset.sum_congr rfl (fun w _ => h_each w), Finset.sum_const, Finset.card_univ]
  simp [Fintype.card_pi, Fintype.card_bool]

/-- **Cross-term factorization**: the cross-term integrand splits into a
short-prefix factor (depending only on the first `r` digits of η at the prefixes
of `w` and `w'`) and a long-prefix factor (depending on η at the longer prefixes
relevant to `P`):
$$ e\!\left(\frac{k\,(j_r(w) - j_r(w') + T_{w,P} - T_{w',P})}{2^r}\right) =
   e\!\left(\frac{k\,(j_r(w) - j_r(w'))}{2^r}\right)
   \cdot e\!\left(\frac{k\,(T_{w,P} - T_{w',P})}{2^r}\right). $$

This factorization is the algebraic prerequisite for the conditional-independence
argument in the variance bound: conditioning on the short-prefix coordinates
fixes `j_r(w), j_r(w')`, leaving only the long-prefix factor to be integrated
out (where `T_{w,P}` and `T_{w',P}` depend on disjoint coordinate sets, hence
are independent). -/
@[category API, AMS 11]
lemma apssvBlockSum_cross_term_factor (η : List Bool → Bool) (P r k : ℕ)
    (w w' : Fin r → Bool) :
    e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ) +
          apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) =
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) *
      e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) := by
  rw [← e_add]; congr 1; ring

/-- **Diagonal/off-diagonal split** of the L² expansion:
$$ \|B_{P, r}(k)\|^2 = 2^r + \sum_{w} \sum_{w' \ne w} e\!\left(\frac{k \cdot
   (j_r(w) - j_r(w') + T_{w,P} - T_{w',P})}{2^r}\right). $$

The diagonal contribution is $2^r$ (each $|f_w| = 1$), and the cross-term sum
is what the probabilistic argument has to control. Taking expectations:
$$ \mathbb{E}[\|B\|^2] = 2^r + \mathbb{E}\Big[\sum_{w \ne w'} \cdots\Big]. $$
The variance bound `apssvBlockSum_variance_bound` reduces to bounding the
expectation of the cross-term sum by $2^r$ (long-block) or
$2 \cdot 2^{2b - r} - 2^r$ (short-block). -/
@[category API, AMS 11]
lemma apssvBlockSum_norm_sq_split (η : List Bool → Bool) (P r k : ℕ) :
    ((‖apssvBlockSum η P r k‖ ^ 2 : ℝ) : ℂ) =
      (2 : ℂ) ^ r +
      ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ) +
              apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) := by
  rw [apssvBlockSum_norm_sq_eq]
  -- For each w, split the inner sum: ∑ w' ∈ univ = (term at w' = w) + ∑ w' ∈ univ.erase w.
  have h_inner : ∀ w : (Fin r → Bool),
      ∑ w' : (Fin r → Bool), e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ) +
            apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) =
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ) +
            apssvT η w P - apssvT η w P) / (2 : ℝ) ^ r) +
        ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
          e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ) +
              apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) := by
    intro w
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ w)).symm
  rw [Finset.sum_congr rfl (fun w _ => h_inner w)]
  rw [Finset.sum_add_distrib]
  rw [apssvBlockSum_diagonal_sum]

/-- **`B = ∑_w c_w · Y_w`**: per-summand factorization of `apssvBlockSum`.
$$ B_{P, r}(k) = \sum_{w} e\!\left(\frac{k\,j_r(w)}{2^r}\right) \cdot
                       e\!\left(\frac{k\,T_{w, P}}{2^r}\right). $$
Direct `e_add` separation. This is the form used to decompose `B` into a
"phase prefactor" `c_w := e(k j_r(w)/2^r)` times a "Fourier weight"
`Y_w := e(k T_{w, P}/2^r)`. -/
@[category API, AMS 11]
lemma apssvBlockSum_eq_sum_factored (η : List Bool → Bool) (P r k : ℕ) :
    apssvBlockSum η P r k =
      ∑ w : Fin r → Bool,
        e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
        e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) := by
  unfold apssvBlockSum
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show ((k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w P) / (2 : ℝ) ^ r) =
      ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) +
      ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) from by ring]
  rw [e_add]

/-- **Centered decomposition** of `apssvBlockSum`: for any `X : ℂ`,
$$ B_{P, r}(k) - X \cdot J_{\text{sum}} = \sum_w c_w \cdot (Y_w - X), $$
where `J_sum := ∑_w c_w := ∑_w e(k j_r(w)/2^r)` is the sum of phase
prefactors and `Y_w := e(k T_{w, P}/2^r)`. Pure algebraic identity (linearity
of `∑_w c_w` over the constant `X`).

**Use**: instantiate with `X = α := ∫ e(k T_{w₀, P}/2^r) dη` (the Fourier mean,
which is `w`-independent by `apssvT_e_integral_w_invariant`). The resulting
`Z_w := c_w · (Y_w - α)` are *centered* in expectation (`E[Z_w] = E[c_w] · 0 = 0`
by independence of short and long coords) and bounded `|Z_w| ≤ 4π·k/2^r`
(by `apssvT_e_integral_one_sub_norm_le` and `apssvT η w P ∈ [0, 1]`). This is
the `B = α·J_sum + ∑_w Z_w` form used in conditional Bernstein/Hoeffding. -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_decomp (η : List Bool → Bool) (P r k : ℕ) (X : ℂ) :
    apssvBlockSum η P r k -
        X * (∑ w : Fin r → Bool, e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r)) =
      ∑ w : Fin r → Bool,
        e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - X) := by
  rw [apssvBlockSum_eq_sum_factored, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- **Per-summand bound** for the centered decomposition: for any `w`,
$$ \big\| c_w \cdot (Y_w - \alpha) \big\| \le \frac{4 \pi k}{2^r}, $$
where `α := ∫ e(k T_{w₀, P}/2^r) dη` (any reference `w₀`).

Proof: `|c_w| = 1` (unit circle), so `‖c_w · (Y_w - α)‖ = ‖Y_w - α‖`. By the
triangle inequality `‖Y_w - α‖ ≤ ‖Y_w - 1‖ + ‖1 - α‖`. The first term is
`≤ 2π·k·T_{w, P}/2^r ≤ 2π·k/2^r` (Lipschitz of `e` plus
`apssvT_factored_le_one`). The second term is the Fourier coefficient bound
`‖1 - α‖ ≤ 2π·k/2^r` from `apssvT_e_integral_one_sub_norm_le`. Sum:
`‖Y_w - α‖ ≤ 4π·k/2^r`.

**Use**: this is the per-summand magnitude bound feeding Hoeffding's
inequality conditional on `F_{<r}`: `Var(B - E[B|F_{<r}] | F_{<r}) ≤
∑_w ‖Z_w‖² ≤ 2^r · (4π·k/2^r)² = 16π²·k²/2^r`, giving the sub-Gaussian tail
`exp(-t²·2^r/(32π²·k²))`. -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_summand_norm_bound {r : ℕ} (η : List Bool → Bool)
    (P k : ℕ) (w w₀ : Fin r → Bool) :
    ‖e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)‖ ≤
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
  set α : ℂ := ∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure with hα_def
  rw [norm_mul, norm_e, one_mul]
  -- ‖Y_w - α‖ ≤ ‖Y_w - 1‖ + ‖1 - α‖.
  have h_split : ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α‖ ≤
      ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1‖ + ‖(1 : ℂ) - α‖ := by
    have h_id : e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α =
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1) + ((1 : ℂ) - α) := by ring
    rw [h_id]; exact norm_add_le _ _
  -- ‖Y_w - 1‖ ≤ 2π·|k T_w/2^r| ≤ 2π·k/2^r.
  have h_Y_bound : ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1‖ ≤
      2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
    have h := e_sub_one_norm_le_abs ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)
    have hT_nn : 0 ≤ apssvT η w P := apssvT_factored_nonneg P _
    have hT_le : apssvT η w P ≤ 1 := apssvT_factored_le_one P _
    have h_arg_nn : 0 ≤ (k : ℝ) * apssvT η w P / (2 : ℝ) ^ r := by positivity
    have h_arg_le : (k : ℝ) * apssvT η w P / (2 : ℝ) ^ r ≤ (k : ℝ) / (2 : ℝ) ^ r := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ r)
      calc (k : ℝ) * apssvT η w P
          ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hT_le (Nat.cast_nonneg k)
        _ = (k : ℝ) := by ring
    have h_abs_le : |(k : ℝ) * apssvT η w P / (2 : ℝ) ^ r| ≤ (k : ℝ) / (2 : ℝ) ^ r := by
      rw [abs_of_nonneg h_arg_nn]; exact h_arg_le
    calc ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1‖
        ≤ 2 * Real.pi * |(k : ℝ) * apssvT η w P / (2 : ℝ) ^ r| := h
      _ ≤ 2 * Real.pi * ((k : ℝ) / (2 : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left h_abs_le (by positivity)
      _ = 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by ring
  -- ‖1 - α‖ ≤ 2π·k/2^r from apssvT_e_integral_one_sub_norm_le.
  have h_alpha_bound : ‖(1 : ℂ) - α‖ ≤ 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
    rw [hα_def]; exact apssvT_e_integral_one_sub_norm_le w₀ P k r
  -- Sum the two bounds: 2π·k/2^r + 2π·k/2^r = 4π·k/2^r.
  have h_sum : ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - 1‖ + ‖(1 : ℂ) - α‖ ≤
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
    have : 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r + 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r =
        4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by ring
    linarith
  exact h_split.trans h_sum

/-- The integrand `η ↦ e(k · apssvX η n)` is integrable on `apssvEtaMeasure` (bounded by `1`
on a probability space). -/
@[category API, AMS 11]
lemma apssvX_e_integrable (n k : ℕ) :
    MeasureTheory.Integrable (fun η : List Bool → Bool => e ((k : ℝ) * apssvX η n))
      apssvEtaMeasure := by
  have h_continuous_e : Continuous e := by
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  have h_inner : Measurable (fun η : List Bool → Bool => (k : ℝ) * apssvX η n) :=
    (apssvX_measurable n).const_mul _
  refine MeasureTheory.Integrable.of_bound
    (h_continuous_e.measurable.comp h_inner).aestronglyMeasurable 1 ?_
  apply MeasureTheory.ae_of_all
  intro η
  rw [norm_e]

/-- The map `i ↦ apssvPrefix n i` is injective (distinct lengths produce distinct lists). -/
@[category API, AMS 11]
lemma apssvPrefix_injective (n : ℕ) : Function.Injective (apssvPrefix n) := by
  intro i j h
  have hi := apssvPrefix_length n i
  have hj := apssvPrefix_length n j
  rw [h, hj] at hi
  exact hi.symm

/- ## Long-prefix pushforward and `w`-invariance of `α := E[e(k T_{w, P}/2^r)]`

The expectation `α := E[e(k T_{w, P}/2^r)]` doesn't depend on `w`: by the long
pushforward, the law of `(η ↦ η ∘ (apssvWordPrefix w ++ apssvPrefix P ·))` is
the i.i.d. infinitePi measure regardless of `w`. -/

/-- **Single-`w` long-coord pushforward** (standalone, no `w'` paired index):
under `apssvEtaMeasure`, the projection
`η ↦ ℓ ↦ η (apssvWordPrefix w r_param ++ apssvPrefix P ℓ)` has pushforward
equal to `infinitePi (Bernoulli)` over `ℕ`. This is the standalone analogue
of `apssvT_pairIndex_row_pushforward` and does not require a paired `w'` —
useful for the T-marginal w-independence step in the variance bound. -/
@[category API, AMS 11]
lemma apssvT_eta_long_pushforward {r_param : ℕ} (w : Fin r_param → Bool) (P : ℕ) :
    apssvEtaMeasure.map
        (fun η : List Bool → Bool => fun ℓ : ℕ =>
          η (apssvWordPrefix w r_param ++ apssvPrefix P ℓ)) =
      MeasureTheory.Measure.infinitePi (fun _ : ℕ => apssvBoolMeasure) := by
  have h_inj : Function.Injective
      (fun ℓ : ℕ => apssvWordPrefix w r_param ++ apssvPrefix P ℓ) :=
    (List.append_right_injective _).comp (apssvPrefix_injective P)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
        (fun _ => apssv_eta_coord_measurable _)).mp
      (apssv_eta_iIndepFun.precomp h_inj)]
  congr 1; funext ℓ
  exact apssv_eta_coord_law _

/-- **T-marginal pushforward identity**: for any `w`, the integral of
`η ↦ e(k · apssvT η w P / 2^r)` over `apssvEtaMeasure` factors through the
infinitePi-pushforward identity, equaling
`∫_σ e(k · apssvT_factored P σ / 2^r) d(infinitePi (Bernoulli))`. The RHS
is manifestly `w`-independent — this is the lemma underlying `α := ∫ e(k T_w/2^r)`
being the same constant for all `w` (key for the variance-bound calculation). -/
@[category API, AMS 11]
lemma apssvT_e_integral_via_pushforward {r_param : ℕ} (w : Fin r_param → Bool)
    (P k r : ℕ) :
    ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure =
    ∫ σ, e ((k : ℝ) * apssvT_factored P σ / (2 : ℝ) ^ r)
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => apssvBoolMeasure)) := by
  -- Rewrite the integrand pointwise via apssvT_eq_factored.
  have h_pw : ∀ η : List Bool → Bool,
      e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) =
      e ((k : ℝ) * apssvT_factored P
        (fun ℓ : ℕ => η (apssvWordPrefix w r_param ++ apssvPrefix P ℓ)) / (2 : ℝ) ^ r) := by
    intro η; rw [apssvT_eq_factored]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pw)]
  -- The integrand is a measurable function ∘ projection; use integral_map.
  have h_continuous_e : Continuous e := by
    unfold e; exact Complex.continuous_exp.comp (by continuity)
  have h_F_meas : Measurable (fun σ : ℕ → Bool =>
      e ((k : ℝ) * apssvT_factored P σ / (2 : ℝ) ^ r)) :=
    h_continuous_e.measurable.comp
      (Measurable.div_const (Measurable.const_mul (apssvT_factored_measurable P) _) _)
  have h_proj_meas : Measurable (fun η : List Bool → Bool => fun ℓ : ℕ =>
      η (apssvWordPrefix w r_param ++ apssvPrefix P ℓ)) :=
    measurable_pi_lambda _ (fun _ => apssv_eta_coord_measurable _)
  have h_map := MeasureTheory.integral_map (μ := apssvEtaMeasure)
    (φ := fun η : List Bool → Bool => fun ℓ : ℕ =>
      η (apssvWordPrefix w r_param ++ apssvPrefix P ℓ))
    (f := fun σ : ℕ → Bool => e ((k : ℝ) * apssvT_factored P σ / (2 : ℝ) ^ r))
    h_proj_meas.aemeasurable h_F_meas.aestronglyMeasurable
  -- h_map : ∫ σ, F σ ∂(μ.map proj) = ∫ η, F (proj η) ∂μ
  rw [← h_map, apssvT_eta_long_pushforward w P]

/-- **T-marginal w-equality**: for any two `w₁, w₂ : Fin r_param → Bool` (no
disjointness needed), `∫ e(k T(η, w₁, P)/2^r) = ∫ e(k T(η, w₂, P)/2^r)`.
Both equal `∫_σ e(k apssvT_factored P σ /2^r) d(infinitePi (Bernoulli))` by
`apssvT_e_integral_via_pushforward`, which is manifestly w-independent. -/
@[category API, AMS 11]
lemma apssvT_e_integral_w_invariant {r_param : ℕ} (w₁ w₂ : Fin r_param → Bool)
    (P k r : ℕ) :
    ∫ η, e ((k : ℝ) * apssvT η w₁ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure =
    ∫ η, e ((k : ℝ) * apssvT η w₂ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure := by
  rw [apssvT_e_integral_via_pushforward w₁ P k r,
      apssvT_e_integral_via_pushforward w₂ P k r]

/-- **T-marginal w-equality, conjugate version**: for any two `w₁, w₂`, the
"negated" T-marginal integrals coincide:
`∫ e(-(k T_w₁/2^r)) = ∫ e(-(k T_w₂/2^r))`. Reduce via `conj_e` and `integral_conj`
to the positive version `apssvT_e_integral_w_invariant`. -/
@[category API, AMS 11]
lemma apssvT_e_integral_neg_w_invariant {r_param : ℕ} (w₁ w₂ : Fin r_param → Bool)
    (P k r : ℕ) :
    ∫ η, e (-((k : ℝ) * apssvT η w₁ P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure =
    ∫ η, e (-((k : ℝ) * apssvT η w₂ P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure := by
  have h_conj : ∀ w : Fin r_param → Bool, ∀ η : List Bool → Bool,
      e (-((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) =
      (starRingEnd ℂ) (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := by
    intro w η; rw [e_neg, ← conj_e]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (h_conj w₁)),
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (h_conj w₂)),
      integral_conj, integral_conj,
      apssvT_e_integral_w_invariant w₁ w₂ P k r]

/-- **Cross-term T-integral as a w-independent constant**: for any `w ≠ w'`,
the cross-term integral `∫ e(k(T_w - T_w')/2^r)` factors through a fixed
reference `w₀` as `α · conj(α)` where `α := ∫ e(k T_{w₀}/2^r)`. The RHS is
manifestly independent of the choice of pair `(w, w')`.

Combines `apssvBlockSum_T_diff_E_factor` (which factors using
`apssvT_indepFun_of_ne` via the apssvT_pairIndex machinery) with the two
w-invariance lemmas to substitute both factors. -/
@[category API, AMS 11]
lemma apssvBlockSum_T_diff_E_constant {r_param : ℕ} (w w' w₀ : Fin r_param → Bool)
    (hww' : w ≠ w') (P k : ℕ) :
    ∫ η, e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r_param)
        ∂apssvEtaMeasure =
      (∫ η, e ((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r_param) ∂apssvEtaMeasure) *
      (∫ η, e (-((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r_param)) ∂apssvEtaMeasure) := by
  rw [apssvBlockSum_T_diff_E_factor w w' hww' P k,
      apssvT_e_integral_w_invariant w w₀ P k r_param,
      apssvT_e_integral_neg_w_invariant w' w₀ P k r_param]

/- ## `apssvX_part`: telescoped truncation toward `∫ e(k · apssvX) = 0`

To compute `∫ e(k · apssvX η n) dη` for `k ≥ 1`, we truncate `apssvX` to its
first `N` binary digits, evaluate the integral via Bernoulli digit-by-digit
factoring, and pass to the limit. -/

/-- Truncation of `apssvX η n` to its first `N` digits (a finite sum). -/
@[category API, AMS 11]
noncomputable def apssvX_part (η : List Bool → Bool) (n N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    (if (n.testBit i).xor (η (apssvPrefix n i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)

@[category API, AMS 11]
lemma apssvX_part_zero (η : List Bool → Bool) (n : ℕ) : apssvX_part η n 0 = 0 := by
  unfold apssvX_part; simp

@[category API, AMS 11]
lemma apssvX_part_succ (η : List Bool → Bool) (n N : ℕ) :
    apssvX_part η n (N + 1) =
      apssvX_part η n N +
        (if (n.testBit N).xor (η (apssvPrefix n N)) then (1 : ℝ) else 0) / 2 ^ (N + 1) := by
  unfold apssvX_part
  rw [Finset.sum_range_succ]

/-- **Generalized partial-sum factorization** for an arbitrary injection
`φ : ℕ → List Bool` of η-coordinates:
$$ \mathbb{E}\!\left[e\!\left(k \!\cdot\! \sum_{i < N} \frac{n.\!testBit_i \oplus \eta(\varphi i)}{2^{i+1}}\right)\right]
   = \prod_{i < N} \frac{1 + e(k / 2^{i+1})}{2}. $$

The proof is identical to `apssvX_part_integral` but parameterized by the
injection. Specializes to:
* `apssvX_part_integral` at `φ = apssvPrefix n`,
* the upcoming `apssvT` partial-sum factorization at
  `φ = (apssvWordPrefix w r ++ apssvPrefix P ·)`. -/
@[category API, AMS 11]
lemma apssv_eta_part_integral (n N k : ℕ) (φ : ℕ → List Bool)
    (hφ : Function.Injective φ) :
    ∫ η, e ((k : ℝ) *
      ∑ i ∈ Finset.range N,
        (if (n.testBit i).xor (η (φ i)) then (1 : ℝ) else 0) / 2 ^ (i + 1))
        ∂apssvEtaMeasure =
      ∏ i ∈ Finset.range N, (1 + e ((k : ℝ) / 2 ^ (i + 1))) / 2 := by
  -- Pointwise: e(k · ∑_i x_i) = ∏_i e(k · x_i) using e_add iteratively.
  have h_e_factor : ∀ η : List Bool → Bool, e ((k : ℝ) * ∑ i ∈ Finset.range N,
        (if (n.testBit i).xor (η (φ i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)) =
      ∏ i ∈ Finset.range N, e ((k : ℝ) *
        ((if (n.testBit i).xor (η (φ i)) then (1 : ℝ) else 0) / 2 ^ (i + 1))) := by
    intro η
    induction N with
    | zero => simp [e_zero]
    | succ N ih =>
        rw [Finset.sum_range_succ, Finset.prod_range_succ, mul_add, e_add, ih]
  rw [show (∫ η, e ((k : ℝ) * ∑ i ∈ Finset.range N,
        (if (n.testBit i).xor (η (φ i)) then (1 : ℝ) else 0) / 2 ^ (i + 1))
          ∂apssvEtaMeasure) =
        ∫ η, ∏ i ∈ Finset.range N, e ((k : ℝ) *
          ((if (n.testBit i).xor (η (φ i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)))
            ∂apssvEtaMeasure from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_e_factor)]
  simp_rw [← Fin.prod_univ_eq_prod_range (n := N)]
  let g : Fin N → List Bool := fun i => φ i.val
  have hg_inj : Function.Injective g := fun i j hij => Fin.ext (hφ hij)
  have h_iIndep := apssv_eta_iIndepFun.precomp hg_inj
  set f : Fin N → Bool → ℂ := fun i b =>
    e ((k : ℝ) * (if (n.testBit i.val).xor b then (1 : ℝ) else 0) / 2 ^ (i.val + 1)) with hf_def
  set X : Fin N → (List Bool → Bool) → Bool := fun i η => η (g i) with hX_def
  have h_factor_eq : (fun η => ∏ i : Fin N, e ((k : ℝ) *
        ((if (n.testBit i.val).xor (η (φ i.val)) then (1 : ℝ) else 0) /
          2 ^ (i.val + 1)))) =
      (fun η => ∏ i : Fin N, f i (X i η)) := by
    funext η
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hf_def, hX_def]
    show _ = e ((k : ℝ) * (if (n.testBit i.val).xor (η (φ i.val))
        then (1:ℝ) else 0) / 2 ^ (i.val + 1))
    congr 1; ring
  rw [h_factor_eq]
  have hX_meas : ∀ i, AEMeasurable (X i) apssvEtaMeasure :=
    fun i => (apssv_eta_coord_measurable (g i)).aemeasurable
  have hf_strong : ∀ i, MeasureTheory.AEStronglyMeasurable (f i)
      (apssvEtaMeasure.map (X i)) :=
    fun i => (Measurable.of_discrete : Measurable (f i)).aestronglyMeasurable
  rw [h_iIndep.integral_fun_prod_comp hX_meas hf_strong]
  refine Finset.prod_congr rfl fun i _ => ?_
  show ∫ η, f i (X i η) ∂apssvEtaMeasure = (1 + e ((k : ℝ) / 2 ^ (i.val + 1))) / 2
  rw [hf_def, hX_def]
  show ∫ η, e ((k : ℝ) *
      (if (n.testBit i.val).xor (η (φ i.val)) then (1 : ℝ) else 0) /
        2 ^ (i.val + 1)) ∂apssvEtaMeasure = _
  exact apssv_eta_at_coord_summand_integral n k i.val (φ i.val)

/-- **Partial-sum factorization (Step 1 of [APSSV26b Prop 3.5])**: specialization of
`apssv_eta_part_integral` at the `apssvPrefix n` injection. -/
@[category API, AMS 11]
lemma apssvX_part_integral (n N k : ℕ) :
    ∫ η, e ((k : ℝ) * apssvX_part η n N) ∂apssvEtaMeasure =
      ∏ i ∈ Finset.range N, (1 + e ((k : ℝ) / 2 ^ (i + 1))) / 2 :=
  apssv_eta_part_integral n N k (apssvPrefix n) (apssvPrefix_injective n)

/-- **`apssvT` partial-sum factorization**: specialization of
`apssv_eta_part_integral` at `φ ℓ = apssvWordPrefix w r ++ apssvPrefix P ℓ`,
with `n = P` (so `n.testBit i = P.testBit i`).

Concretely:
$$ \mathbb{E}\!\left[e\!\left(k \cdot \sum_{i<N} \frac{P.\!testBit_i \oplus
\eta(w \mathbin{+\!\!+} \text{apssvPrefix}\,P\,i)}{2^{i+1}}\right)\right]
= \prod_{i<N} \frac{1 + e(k/2^{i+1})}{2}. $$

This computes the expectation of `e(k · apssvT_part_finite)` for any finite
truncation of the `apssvT` tsum. Passing to the limit (DCT, mirroring Step 3
for `apssvX`) gives the value of `E[e(k · T(η, w, P))]` as an infinite product.
After scaling by `1/2^r` (the divisor in the cross-term integrand of the
variance bound), this becomes the form of `α := ∫ e(k · T(η,w,P)/2^r) dη`. -/
@[category API, AMS 11]
lemma apssvT_part_integral_aux {r_param : ℕ} (w : Fin r_param → Bool) (P N k : ℕ) :
    ∫ η, e ((k : ℝ) *
      ∑ i ∈ Finset.range N,
        (if (P.testBit i).xor (η (apssvWordPrefix w r_param ++ apssvPrefix P i)) then
          (1 : ℝ) else 0) / 2 ^ (i + 1))
        ∂apssvEtaMeasure =
      ∏ i ∈ Finset.range N, (1 + e ((k : ℝ) / 2 ^ (i + 1))) / 2 := by
  refine apssv_eta_part_integral P N k
    (fun i => apssvWordPrefix w r_param ++ apssvPrefix P i) ?_
  -- Injectivity of i ↦ apssvWordPrefix w r ++ apssvPrefix P i:
  -- the second component (apssvPrefix P) is injective by length, and the first
  -- is constant in i, so the concat is injective.
  intro i j h
  have h' : apssvWordPrefix w r_param ++ apssvPrefix P i =
            apssvWordPrefix w r_param ++ apssvPrefix P j := h
  -- Both lists start with the same r-length prefix, so equality of concats forces
  -- equality of the apssvPrefix P · part.
  have h_drop : (apssvWordPrefix w r_param ++ apssvPrefix P i).drop r_param =
      (apssvWordPrefix w r_param ++ apssvPrefix P j).drop r_param := by rw [h']
  rw [List.drop_left' (apssvWordPrefix_length w r_param),
      List.drop_left' (apssvWordPrefix_length w r_param)] at h_drop
  exact apssvPrefix_injective P h_drop

/-- For every `k ≥ 1`, there exists an index `i` at which the centering factor
`1 + e(k/2^(i+1))` vanishes — namely `i = v_2(k)`, the 2-adic valuation of `k`,
where `k/2^(i+1)` is a half-integer plus integer and `e` of that is `-1`. -/
@[category API, AMS 11]
lemma apssv_exists_factor_zero (k : ℕ) (hk : 1 ≤ k) :
    ∃ i : ℕ, (1 : ℂ) + e ((k : ℝ) / 2 ^ (i + 1)) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.even_or_odd k with ⟨k', hkeq⟩ | hodd
    · -- k = 2k' (even). By IH on k', there's i' with (1 + e(k'/2^(i'+1))) = 0.
      -- Then (1 + e(2k'/2^(i'+2))) = (1 + e(k'/2^(i'+1))) = 0.
      have hk2 : k = 2 * k' := by omega
      subst hk2
      have hk'_pos : 1 ≤ k' := by omega
      have hk'_lt : k' < 2 * k' := by omega
      obtain ⟨i', hi'⟩ := ih k' hk'_lt hk'_pos
      refine ⟨i' + 1, ?_⟩
      have h_eq : ((2 * k' : ℕ) : ℝ) / 2 ^ (i' + 1 + 1) = (k' : ℝ) / 2 ^ (i' + 1) := by
        push_cast; field_simp; ring
      rw [h_eq]; exact hi'
    · -- k odd: factor at i = 0 is 0 by `e_half_odd`.
      refine ⟨0, ?_⟩
      have h_eq : (k : ℝ) / 2 ^ (0 + 1) = (k : ℝ) / 2 := by norm_num
      rw [h_eq]
      exact e_half_odd k hodd

/-- **Vanishing of the partial-sum integral (Step 2 of [APSSV26b Prop 3.5])**: for
every `k ≥ 1`, there exists `N₀` such that for all `N ≥ N₀ + 1`, the random partial
sum is *centered*:
$$ \mathbb{E}\big[e(k \cdot \mathrm{apssvX\_part}\,\eta\,n\,N)\big] = 0. $$

The argument: by `apssv_exists_factor_zero`, some factor `(1 + e(k/2^(i+1)))/2`
in the product expression for the integral is zero. Once we take `N` large enough
to include this index, the entire product vanishes. -/
@[category API, AMS 11]
lemma apssvX_part_integral_eq_zero (n k : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∫ η, e ((k : ℝ) * apssvX_part η n N) ∂apssvEtaMeasure = 0 := by
  obtain ⟨i₀, hi₀⟩ := apssv_exists_factor_zero k hk
  refine ⟨i₀, fun N hN => ?_⟩
  rw [apssvX_part_integral]
  -- The factor at index i₀ is 0; that kills the product.
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hN) ?_
  rw [hi₀, zero_div]

/-- `apssvX_part η n N → apssvX η n` as `N → ∞` for each fixed `η, n`: the partial
sums converge to the tsum. -/
@[category API, AMS 11]
lemma apssvX_part_tendsto (η : List Bool → Bool) (n : ℕ) :
    Filter.Tendsto (fun N : ℕ => apssvX_part η n N) Filter.atTop (nhds (apssvX η n)) := by
  unfold apssvX_part apssvX
  exact (apssvX_summable η n).hasSum.tendsto_sum_nat

/-- **Centering of the full random sum (Step 3 of [APSSV26b Prop 3.5])**: for
every `k ≥ 1`,
$$ \mathbb{E}\big[e(k \cdot \mathrm{apssvX}\,\eta\,n)\big] = 0. $$

The proof uses the bounded convergence theorem: the partial-sum integrand
`e(k · apssvX_part η n N)` converges pointwise (in `N`) to `e(k · apssvX η n)`
and is bounded by `1`. Combined with `apssvX_part_integral_eq_zero` (the partial-sum
integral is eventually 0), the limit is `0`. -/
@[category API, AMS 11]
lemma apssvX_integral_eq_zero (n k : ℕ) (hk : 1 ≤ k) :
    ∫ η, e ((k : ℝ) * apssvX η n) ∂apssvEtaMeasure = 0 := by
  have h_continuous_e : Continuous e := by
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  -- Define the partial-sum integrand sequence.
  set F : ℕ → (List Bool → Bool) → ℂ :=
    fun N η => e ((k : ℝ) * apssvX_part η n N) with hF_def
  set f : (List Bool → Bool) → ℂ := fun η => e ((k : ℝ) * apssvX η n) with hf_def
  -- DCT: ∫ F N → ∫ f.
  have h_F_meas : ∀ N, MeasureTheory.AEStronglyMeasurable (F N) apssvEtaMeasure := by
    intro N
    apply Measurable.aestronglyMeasurable
    apply h_continuous_e.measurable.comp
    apply Measurable.const_mul
    -- apssvX_part is a finite sum of measurable functions.
    apply Finset.measurable_sum
    intros i _
    exact apssvX_summand_measurable n i
  have h_bound : ∀ N, ∀ᵐ η ∂apssvEtaMeasure, ‖F N η‖ ≤ 1 :=
    fun N => MeasureTheory.ae_of_all _ (fun η => by rw [hF_def]; exact (norm_e _).le)
  have h_bound_int : MeasureTheory.Integrable (fun _ : List Bool → Bool => (1 : ℝ))
      apssvEtaMeasure := MeasureTheory.integrable_const _
  have h_lim : ∀ᵐ η ∂apssvEtaMeasure,
      Filter.Tendsto (fun N => F N η) Filter.atTop (nhds (f η)) := by
    apply MeasureTheory.ae_of_all
    intro η
    rw [hF_def, hf_def]
    apply h_continuous_e.tendsto _ |>.comp
    exact ((apssvX_part_tendsto η n).const_mul (k : ℝ)).comp tendsto_id |>.congr (fun _ => rfl)
  have h_tendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := F) (f := f) (μ := apssvEtaMeasure) (fun _ => 1) h_F_meas h_bound_int h_bound h_lim
  -- The partial-sum integral is eventually 0.
  obtain ⟨N₀, hN₀⟩ := apssvX_part_integral_eq_zero n k hk
  have h_eventually : ∀ᶠ N in Filter.atTop, ∫ η, F N η ∂apssvEtaMeasure = 0 :=
    Filter.eventually_atTop.mpr ⟨N₀ + 1, fun N hN => hN₀ N (by omega)⟩
  have h_const : Filter.Tendsto (fun N => ∫ η, F N η ∂apssvEtaMeasure) Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventually) (tendsto_const_nhds)
  exact tendsto_nhds_unique h_tendsto h_const

/-- `e x = 1 ↔ x ∈ ℤ`: an `e`-form of `Complex.exp_eq_one_iff`. -/
@[category API, AMS 11]
lemma e_eq_one_iff_int (x : ℝ) : e x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hI_ne : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    have h_eq : ((2 * Real.pi * x : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi : ℝ) :=
      mul_right_cancel₀ hI_ne (hn.trans (by push_cast; ring))
    have h_eq' : ((2 * Real.pi * x : ℝ) : ℝ) = (n : ℝ) * (2 * Real.pi) := by
      exact_mod_cast h_eq
    have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have : x = (n : ℝ) := by
      field_simp at h_eq'
      linarith
    exact this
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

/- ## j-factor double sum and centered decomposition `B = α · J_sum + ∑_w Z_w`

Two ingredients of the variance / centered-decomposition argument:

* `apssv_j_factor_double_sum`: the deterministic identity
  `∑_{w ≠ w'} e(k(j_r(w) - j_r(w'))/2^r) = -2^r` in the long-block regime
  `1 ≤ k < 2^r`, generalised modulo `2^r` so it covers `k % 2^r ≥ 1` too.
* `apssv_alpha_J_sum_eq_zero` (deterministic): `α · J_sum = 0` always — by case
  split on `1 ≤ k % 2^r` (J_sum = 0 by root-of-unity cancellation) vs
  `2^r ∣ k` (α = 0 by bit-flip symmetry).
* `apssvBlockSum_eq_centered_sum`: `B = α · J_sum + ∑_w c_w · (Y_w - α)`. -/

/-- Geometric-sum cancellation at roots of unity:
$\sum_{j=0}^{2^r - 1} e(k \cdot j / 2^r) = 0$ for $1 \le k < 2^r$.

Key identity for the APSSV "long-block" regime: when $r > \log_2 k$, the sum
$\sum_w e(k \cdot j_r(w) / 2^r)$ collapses to zero (the apssvJ bijection turns
$w \mapsto j_r(w)$ into a permutation of $\{0, \ldots, 2^r - 1\}$). The remaining
magnitude comes from the tail $T_{w,P}$. -/
@[category API, AMS 11]
lemma apssv_geom_sum_at_root_eq_zero (k r : ℕ) (hk : 1 ≤ k) (hkr : k < 2 ^ r) :
    ∑ j ∈ Finset.range (2 ^ r), e ((k : ℝ) * j / 2 ^ r) = 0 := by
  set ω : ℂ := e ((k : ℝ) / 2 ^ r) with hω_def
  -- Factor: e(k·j/2^r) = (e(k/2^r))^j = ω^j (using e_pow_natCast).
  have h_factor : ∀ j : ℕ, e ((k : ℝ) * j / 2 ^ r) = ω ^ j := by
    intro j
    rw [hω_def, e_pow_natCast]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => h_factor j)]
  -- ω^(2^r) = e(k) = 1.
  have h_ω_pow : ω ^ (2 ^ r) = 1 := by
    rw [← h_factor (2 ^ r)]
    rw [show ((k : ℝ) * (2 ^ r : ℕ) / 2 ^ r) = (k : ℝ) by push_cast; field_simp]
    exact e_natCast k
  -- ω ≠ 1: e(k/2^r) = 1 iff k/2^r ∈ ℤ. For 1 ≤ k < 2^r, k/2^r ∈ (0, 1), not integer.
  have h_ω_ne_one : ω ≠ 1 := by
    intro h
    rw [hω_def, e_eq_one_iff_int] at h
    obtain ⟨n, hn⟩ := h
    have h2r_pos : (0 : ℝ) < 2 ^ r := by positivity
    have h_kr_pos : (0 : ℝ) < (k : ℝ) / 2 ^ r := div_pos (by exact_mod_cast hk) h2r_pos
    have h_kr_lt_1 : (k : ℝ) / 2 ^ r < 1 := by
      rw [div_lt_one h2r_pos]; exact_mod_cast hkr
    have h_n_pos : (0 : ℝ) < n := by rw [← hn]; exact h_kr_pos
    have h_n_lt_1 : (n : ℝ) < 1 := by rw [← hn]; exact h_kr_lt_1
    have hn_pos : 0 < n := by exact_mod_cast h_n_pos
    have hn_lt : n < 1 := by exact_mod_cast h_n_lt_1
    omega
  rw [geom_sum_eq h_ω_ne_one, h_ω_pow, sub_self, zero_div]

/-- **Conjugate geometric-sum cancellation**: for `1 ≤ k < 2^r`,
$\sum_{j=0}^{2^r - 1} e(-k \cdot j / 2^r) = 0$. Follows from
`apssv_geom_sum_at_root_eq_zero` via complex conjugation
(`conj_e θ = e(-θ)` and `conj` is additive). -/
@[category API, AMS 11]
lemma apssv_geom_sum_neg_at_root_eq_zero (k r : ℕ) (hk : 1 ≤ k) (hkr : k < 2 ^ r) :
    ∑ j ∈ Finset.range (2 ^ r), e (-((k : ℝ) * j / 2 ^ r)) = 0 := by
  have h_each : ∀ j : ℕ, e (-((k : ℝ) * j / 2 ^ r)) =
      (starRingEnd ℂ) (e ((k : ℝ) * j / 2 ^ r)) := by
    intro j
    rw [conj_e, ← e_neg]
  rw [Finset.sum_congr rfl (fun j _ => h_each j)]
  rw [← map_sum (starRingEnd ℂ)]
  rw [apssv_geom_sum_at_root_eq_zero k r hk hkr]
  exact map_zero _

/-- **j-factor double-sum collapse (long-block regime, deterministic)**: for
`1 ≤ k < 2^r`,
$$ \sum_{w \ne w'} e\!\left(\frac{k\,(j_r(w) - j_r(w'))}{2^r}\right) = -2^r. $$

This is the deterministic algebraic identity behind the variance bound's
"long-block cancellation". Argument:

1. Split the off-diagonal as full double sum minus diagonal:
   $\sum_{w \ne w'} = \sum_{w, w'} - \sum_w 1 = \sum_{w, w'} - 2^r$.
2. Factor the full double sum:
   $\sum_{w, w'} e(k(j(w) - j(w'))/2^r) =
    (\sum_w e(k j(w)/2^r))(\sum_{w'} e(-k j(w')/2^r))$.
3. Reindex each factor via `apssvJ_bijective`: $w \mapsto j_r(w)$ is a bijection
   $(Fin\,r \to Bool) \cong Fin\,2^r$, so each sum becomes a sum over
   $Fin\,2^r$.
4. For $1 \le k < 2^r$, both geometric sums vanish by
   `apssv_geom_sum_at_root_eq_zero` and `apssv_geom_sum_neg_at_root_eq_zero`.
5. Result: $0 \cdot 0 - 2^r = -2^r$.

This is purely deterministic — no probability needed — and is the key step
that lets the variance bound side-step conditional expectation. -/
@[category API, AMS 11]
lemma apssv_j_factor_double_sum (η : List Bool → Bool) (r k : ℕ) (hk : 1 ≤ k)
    (hkr : k < 2 ^ r) :
    ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) =
      -(2 : ℂ) ^ r := by
  -- Step 0: pointwise factorization e(k(a-b)/2^r) = e(k·a/2^r) · e(-k·b/2^r).
  have h_pw : ∀ w w' : Fin r → Bool,
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) =
        e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
        e (-((k : ℝ) * (apssvJ η r w' : ℝ) / (2 : ℝ) ^ r)) := by
    intro w w'
    rw [← e_add]; congr 1; ring
  -- Step 1: rewrite every off-diagonal term using h_pw.
  -- And split off-diagonal = full - diag.
  have h_diag_one : ∀ w : Fin r → Bool,
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) / (2 : ℝ) ^ r) = 1 := by
    intro w
    rw [show ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) = 0 from by ring]
    rw [show ((k : ℝ) * 0 / (2 : ℝ) ^ r) = 0 from by ring]
    exact e_zero
  have h_off_diag : ∀ w : Fin r → Bool,
      ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) =
      (∑ w' : Fin r → Bool,
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)) - 1 := by
    intro w
    have h_add := Finset.add_sum_erase (Finset.univ : Finset (Fin r → Bool))
      (fun w' => e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r))
      (Finset.mem_univ w)
    simp only at h_add
    rw [h_diag_one w] at h_add
    -- 1 + S = T → S = T - 1.
    linear_combination h_add
  -- The outer sum.
  rw [Finset.sum_congr rfl (fun w _ => h_off_diag w)]
  rw [Finset.sum_sub_distrib]
  -- ∑ w, 1 = 2^r (in ℂ).
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Goal: (∑ w, ∑ w', e(...)) - (Fin.card r → Bool) • 1 = -2^r.
  -- The full double sum factors and reduces to 0 · 0 = 0.
  have h_full : ∑ w : (Fin r → Bool), ∑ w' : (Fin r → Bool),
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) = 0 := by
    rw [Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => h_pw w w'))]
    -- ∑ w, ∑ w', f(w) · g(w') = (∑ w, f(w)) · (∑ w', g(w')).
    rw [show (∑ w : (Fin r → Bool), ∑ w' : (Fin r → Bool),
            e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
              e (-((k : ℝ) * (apssvJ η r w' : ℝ) / (2 : ℝ) ^ r))) =
        (∑ w : (Fin r → Bool), e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r)) *
        (∑ w' : (Fin r → Bool), e (-((k : ℝ) * (apssvJ η r w' : ℝ) / (2 : ℝ) ^ r))) from by
      rw [Finset.sum_mul_sum]]
    -- Reindex each factor via apssvJ_bijective.
    let φ : (Fin r → Bool) ≃ Fin (2 ^ r) :=
      Equiv.ofBijective _ (apssvJ_bijective η r)
    have h_reindex_pos :
        (∑ w : (Fin r → Bool), e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r)) =
        ∑ m : Fin (2 ^ r), e ((k : ℝ) * (m : ℝ) / (2 : ℝ) ^ r) := by
      apply Fintype.sum_equiv φ
      intro w
      show _ = e ((k : ℝ) * ((φ w).val : ℝ) / (2 : ℝ) ^ r)
      rfl
    have h_reindex_neg :
        (∑ w : (Fin r → Bool), e (-((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r))) =
        ∑ m : Fin (2 ^ r), e (-((k : ℝ) * (m : ℝ) / (2 : ℝ) ^ r)) := by
      apply Fintype.sum_equiv φ
      intro w
      show _ = e (-((k : ℝ) * ((φ w).val : ℝ) / (2 : ℝ) ^ r))
      rfl
    rw [h_reindex_pos, h_reindex_neg]
    -- Convert ∑ m : Fin (2^r) to ∑ m ∈ Finset.range (2^r).
    rw [show (∑ m : Fin (2 ^ r), e ((k : ℝ) * (m : ℝ) / (2 : ℝ) ^ r)) =
        ∑ m ∈ Finset.range (2 ^ r), e ((k : ℝ) * (m : ℝ) / (2 : ℝ) ^ r) from
      Fin.sum_univ_eq_sum_range (fun j : ℕ =>
        e ((k : ℝ) * (j : ℝ) / (2 : ℝ) ^ r)) (2 ^ r)]
    rw [show (∑ m : Fin (2 ^ r), e (-((k : ℝ) * (m : ℝ) / (2 : ℝ) ^ r))) =
        ∑ m ∈ Finset.range (2 ^ r), e (-((k : ℝ) * (m : ℝ) / (2 : ℝ) ^ r)) from
      Fin.sum_univ_eq_sum_range (fun j : ℕ =>
        e (-((k : ℝ) * (j : ℝ) / (2 : ℝ) ^ r))) (2 ^ r)]
    rw [apssv_geom_sum_at_root_eq_zero k r hk hkr]
    rw [apssv_geom_sum_neg_at_root_eq_zero k r hk hkr]
    ring
  rw [h_full]
  ring

/-- **Generalized j-factor double-sum identity**: for any `k` with `k % 2^r ≥ 1`,
$$ \sum_{w \ne w'} e\big(k \cdot (j_r(w) - j_r(w'))/2^r\big) = -2^r. $$

This generalizes `apssv_j_factor_double_sum` (which required `k < 2^r`) by reducing
to the case `s := k % 2^r ∈ [1, 2^r)`: since `(k - s)/2^r ∈ ℕ` and
`apssvJ η r w - apssvJ η r w' ∈ ℤ`, the surplus factor
`e((k-s)·(J(w)-J(w'))/2^r) = e(integer) = 1` (by `e_intCast`), so the long-block
identity for `s` carries over verbatim to `k`. -/
@[category API, AMS 11]
lemma apssv_j_factor_double_sum_mod (η : List Bool → Bool) (r k : ℕ)
    (hk_mod : 1 ≤ k % 2 ^ r) :
    ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) =
      -(2 : ℂ) ^ r := by
  have h_2pow_pos : 0 < 2 ^ r := pow_pos (by norm_num : (0 : ℕ) < 2) r
  have hs_lt : k % 2 ^ r < 2 ^ r := Nat.mod_lt k h_2pow_pos
  have h_split : k = (k / 2 ^ r) * 2 ^ r + (k % 2 ^ r) := by
    have h := Nat.div_add_mod k (2 ^ r)
    linarith [h, Nat.mul_comm (2 ^ r) (k / 2 ^ r)]
  -- Pointwise reduction: e(k·D/2^r) = e((k%2^r)·D/2^r) when D ∈ ℤ.
  have h_reduce : ∀ w w' : Fin r → Bool,
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) =
      e (((k % 2 ^ r : ℕ) : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) /
          (2 : ℝ) ^ r) := by
    intro w w'
    set D : ℤ := (apssvJ η r w : ℤ) - (apssvJ η r w' : ℤ) with hD_def
    have hD_real : (apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ) = (D : ℝ) := by
      rw [hD_def]; push_cast; ring
    have h_2pow_ne : ((2 : ℝ) ^ r : ℝ) ≠ 0 := by positivity
    have h_kr : (k : ℝ) = ((k / 2 ^ r : ℕ) : ℝ) * (2 : ℝ) ^ r + ((k % 2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast h_split
    have h_decomp : (k : ℝ) * (D : ℝ) / (2 : ℝ) ^ r =
        ((k / 2 ^ r : ℕ) : ℝ) * (D : ℝ) +
        ((k % 2 ^ r : ℕ) : ℝ) * (D : ℝ) / (2 : ℝ) ^ r := by
      rw [h_kr]; field_simp
    have h_int_arg : ((k / 2 ^ r : ℕ) : ℝ) * (D : ℝ) =
        ((((k / 2 ^ r : ℕ) : ℤ) * D : ℤ) : ℝ) := by
      rw [Int.cast_mul, Int.cast_natCast]
    rw [hD_real, h_decomp, h_int_arg, e_add, e_intCast, one_mul]
  rw [Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => h_reduce w w'))]
  exact apssv_j_factor_double_sum η r (k % 2 ^ r) hk_mod hs_lt

/-- **Phase prefactor sum vanishes (case `1 ≤ k % 2^r`)**:
$$ \sum_{w \in \{0, 1\}^r} e\!\left(\frac{k \,j_r(w)}{2^r}\right) = 0
   \quad \text{for } 1 \le k \bmod 2^r. $$

Proof: write `J := ∑_w c_w` with `c_w := e(k j_r(w)/2^r)`. Then
`J · conj(J) = ∑_{w, w'} c_w · conj(c_{w'}) = ∑_{w, w'} e(k(j_w - j_{w'})/2^r)
            = 2^r + (-2^r) = 0`,
where the diagonal contribution `2^r` comes from `c_w · conj(c_w) = 1` and the
off-diagonal `−2^r` from `apssv_j_factor_double_sum_mod`. Since `J · conj(J) = 0`
in `ℂ` and `J · conj(J) = ‖J‖² ≥ 0`, we have `‖J‖ = 0`, i.e., `J = 0`.

**Use**: in the centered decomposition `B = α · J_sum + ∑_w c_w · (Y_w - α)`,
this kills the bias term `α · J_sum`, leaving `B = ∑_w c_w · (Y_w - α)`
(centered) — the key identity for Hoeffding's inequality. -/
@[category API, AMS 11]
lemma apssv_j_sum_eq_zero (η : List Bool → Bool) (r k : ℕ)
    (hk_mod : 1 ≤ k % 2 ^ r) :
    ∑ w : Fin r → Bool, e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) = 0 := by
  set J : ℂ := ∑ w : Fin r → Bool, e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r)
    with hJ_def
  -- J · conj J = ∑_{w, w'} e(k(j_w - j_{w'})/2^r).
  have h_prod : J * (starRingEnd ℂ) J =
      ∑ w : Fin r → Bool, ∑ w' : Fin r → Bool,
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) := by
    rw [hJ_def, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w' _ => ?_
    -- e(α) * conj(e(β)) = e(α) * e(-β) = e(α - β).
    rw [show (starRingEnd ℂ) (e ((k : ℝ) * (apssvJ η r w' : ℝ) / (2 : ℝ) ^ r)) =
        e (-((k : ℝ) * (apssvJ η r w' : ℝ) / (2 : ℝ) ^ r)) from by rw [e_neg, conj_e]]
    rw [← e_add]
    congr 1; ring
  -- Diagonal sum (w' = w): each term = e(0) = 1, total = 2^r.
  have h_diag_sum : ∑ w : Fin r → Bool,
      e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) / (2 : ℝ) ^ r) =
      (2 : ℂ) ^ r := by
    have h_each : ∀ w : Fin r → Bool,
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) / (2 : ℝ) ^ r) = 1 := by
      intro w
      rw [show ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) = 0 from by ring]
      rw [show ((k : ℝ) * 0 / (2 : ℝ) ^ r) = 0 from by ring]; exact e_zero
    rw [Finset.sum_congr rfl (fun w _ => h_each w)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi,
      Fintype.card_bool, Finset.prod_const, Fintype.card_fin]
    ring
  -- Double sum splits: outer ∑_w of (term at w' = w + ∑_{w' ∈ erase w}).
  have h_double_sum :
      ∑ w : Fin r → Bool, ∑ w' : Fin r → Bool,
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) = 0 := by
    rw [show (∑ w : Fin r → Bool, ∑ w' : Fin r → Bool,
          e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)) =
        (∑ w : Fin r → Bool,
          (e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w : ℝ)) / (2 : ℝ) ^ r) +
            ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
              e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r))) from
        Finset.sum_congr rfl fun w _ =>
          (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ w)).symm]
    rw [Finset.sum_add_distrib, h_diag_sum, apssv_j_factor_double_sum_mod η r k hk_mod]
    ring
  rw [h_double_sum] at h_prod
  -- Convert J · conj J = 0 to normSq J = 0, hence J = 0.
  have h_norm_sq_real : (Complex.normSq J : ℂ) = 0 := by
    rw [← Complex.mul_conj]; exact h_prod
  have h_norm_sq : Complex.normSq J = 0 := by exact_mod_cast h_norm_sq_real
  exact Complex.normSq_eq_zero.mp h_norm_sq

/-- **The centering term `α · J_sum` is identically zero** (any `k ≥ 1`):
$$ \big(\!\!\int e(k T_{w_0, P}/2^r) \,d\eta\big) \cdot \sum_w e(k j_r(w)/2^r) = 0. $$

Case-split: if `1 ≤ k % 2^r`, the phase prefactor sum `J_sum = 0` by
`apssv_j_sum_eq_zero` (deterministic root-of-unity cancellation). If `2^r ∣ k`,
the Fourier mean `α = 0` by `apssvT_e_integral_q_eq_zero` (bit-flip symmetry).

**Use**: combined with the algebraic identity `apssvBlockSum_centered_decomp`
(`B - α·J_sum = ∑_w c_w · (Y_w - α)`), this yields the unified centered form
`B = ∑_w c_w · (Y_w - α)` — the decomposition feeding Hoeffding's inequality. -/
@[category API, AMS 11]
lemma apssv_alpha_J_sum_eq_zero {r : ℕ} (η : List Bool → Bool) (P k : ℕ) (hk : 1 ≤ k)
    (w₀ : Fin r → Bool) :
    (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) *
    (∑ w : Fin r → Bool, e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r)) = 0 := by
  by_cases hk_mod : 1 ≤ k % 2 ^ r
  · -- Case 1: 1 ≤ k % 2^r ⟹ J_sum = 0.
    rw [apssv_j_sum_eq_zero η r k hk_mod, mul_zero]
  · -- Case 2: k % 2^r = 0, i.e., 2^r ∣ k ⟹ α = 0.
    push_neg at hk_mod
    have hkdvd : 2 ^ r ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨q, hq_eq⟩ := hkdvd
    have hq_pos : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq_pos
      · subst hq0; rw [Nat.mul_zero] at hq_eq; omega
      · exact hq_pos
    have hα_zero : (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) = 0 := by
      have h_eq_arg : ∀ η' : List Bool → Bool,
          ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) = (q : ℝ) * apssvT η' w₀ P := by
        intro η'
        have h_2pow_ne : ((2 : ℝ) ^ r : ℝ) ≠ 0 := by positivity
        have h_k_eq : (k : ℝ) = (2 : ℝ) ^ r * (q : ℝ) := by exact_mod_cast hq_eq
        rw [h_k_eq]; field_simp
      rw [show (fun η' : List Bool → Bool => e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r)) =
            (fun η' => e ((q : ℝ) * apssvT η' w₀ P)) from
          funext fun η' => by rw [h_eq_arg η']]
      exact apssvT_e_integral_q_eq_zero w₀ P q hq_pos
    rw [hα_zero, zero_mul]

/-- **Unified centered decomposition** (`B = ∑_w Z_w`): for any `k ≥ 1` and
any reference `w₀ : Fin r → Bool`,
$$ B_{P, r}(k) = \sum_w e\!\left(\frac{k \,j_r(w)}{2^r}\right) \cdot
                       \left(e\!\left(\frac{k \,T_{w, P}}{2^r}\right) - \alpha\right), $$
where `α := ∫ e(k T_{w₀, P}/2^r) dη`.

Combines the algebraic identity `apssvBlockSum_centered_decomp` with the
vanishing of the bias term `apssv_alpha_J_sum_eq_zero`. The summands
`Z_w := c_w · (Y_w - α)` satisfy `‖Z_w‖ ≤ 4π·k/2^r`
(`apssvBlockSum_centered_summand_norm_bound`).

This is the `B = ∑_w Z_w` form needed for Hoeffding's inequality (conditional
on `F_{<r}`): the `Z_w` are conditionally independent and bounded, so the
sub-Gaussian tail `μ{‖B‖ > t} ≤ 4 exp(-t²·2^r/(64π²·k²))` follows. -/
@[category API, AMS 11]
lemma apssvBlockSum_eq_centered_sum {r : ℕ} (η : List Bool → Bool) (P k : ℕ) (hk : 1 ≤ k)
    (w₀ : Fin r → Bool) :
    apssvBlockSum η P r k =
      ∑ w : Fin r → Bool,
        e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) := by
  have h_decomp := apssvBlockSum_centered_decomp η P r k
    (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)
  have h_zero := apssv_alpha_J_sum_eq_zero η P k hk w₀
  linear_combination h_decomp + h_zero

/- ## Variance bounds: `∫ ‖B‖² = 2^r·(1 - ‖α‖²)` formula and three regime forms

Combine the centered decomposition + j-T cross-term independence to get:

* `apssvBlockSum_variance_eq`: the closed form `∫ ‖B‖² = 2^r·(1 - ‖α‖²)`.
* `apssvBlockSum_variance_bound`: `≤ 2 · 2^r` (uses `‖α‖ ≤ 1`).
* `apssvBlockSum_variance_bound_long`: `≤ 4π · k` (uses linear Fourier-coeff
  bound `‖1 - α‖ ≤ 2π · k / 2^r`); the form needed for the long-regime
  sub-Gaussian parameter.
* `apssvBlockSum_variance_bound_short`: `≤ 2 · 2^(2b - r)` for `r ≤ b(k)`. -/

/-- **Variance bound, long-block regime (part of Step 5 of [APSSV26b Prop 3.5])**:
for `r ≥ b(k)`,
$$ \mathbb{E}\big[\|B_{P, r}(k)\|^2\big] \le 2 \cdot 2^r. $$

**Proof sketch** (Lemma 3.6 of [APSSV26b]):

Write $B_{P, r}(k) = \sum_{w \in \{0,1\}^r} f_w(\eta)$ where
$f_w(\eta) = e(k \cdot (j_r(w) + T_{w, P})/2^r)$.

Expanding $\|B\|^2 = B \cdot \overline{B}$:
$$ \|B\|^2 = \sum_{w} 1 + \sum_{w \ne w'} f_w(\eta) \cdot \overline{f_{w'}(\eta)}. $$

The first sum is $2^r$. For the cross terms, observe that $f_w$ depends on $\eta$ at:
* Short prefixes (length $< r$) of $w$, via the $j_r(w)$ factor.
* Long prefixes (length $\ge r$), starting with the "stem" $\eta$-values determined by
  $w$'s last bit and the bits of $P$, via the $T_{w, P}$ factor.

**Cleaner argument (no conditioning needed)**: by `apssvBlockSum_norm_sq_split`,
$\|B\|^2 = 2^r + \sum_{w \ne w'} \text{cross\_term}(w, w')$ where
$\text{cross\_term}(w, w') = e(k(j_r(w) - j_r(w'))/2^r) \cdot e(k(T_{w, P} - T_{w', P})/2^r)
= A(w, w') \cdot B(w, w')$. Then:

1. Take expectation: $\mathbb{E}[\|B\|^2] = 2^r + \sum_{w \ne w'} \mathbb{E}[A \cdot B]$.
2. By `apssvBlockSum_j_T_indepFun`: $A \perp B$, so $\mathbb{E}[A \cdot B] =
   \mathbb{E}[A] \cdot \mathbb{E}[B]$.
3. $\mathbb{E}[B(w, w')] = \alpha \cdot \overline{\alpha} = \|\alpha\|^2$ where
   $\alpha := \mathbb{E}[e(k T_{w,P}/2^r)]$ is `w`-independent (by the row pushforward
   in `apssvT_pairIndex_row_pushforward`); see `apssvBlockSum_T_diff_E_factor`.
4. Sum: $\sum_{w \ne w'} \mathbb{E}[A] \cdot \mathbb{E}[B] = \|\alpha\|^2 \cdot
   \sum_{w \ne w'} \mathbb{E}[A]
   = \|\alpha\|^2 \cdot \mathbb{E}[\sum_{w \ne w'} A(w, w')]$ (linearity).
5. $\sum_{w \ne w'} A(w, w') = -2^r$ deterministically (by `apssv_j_factor_double_sum`,
   using the apssvJ bijection + `apssv_geom_sum_at_root_eq_zero` in the long-block
   regime $1 \le k < 2^r$).
6. Combine: $\mathbb{E}[\|B\|^2] = 2^r - \|\alpha\|^2 \cdot 2^r = 2^r(1 - \|\alpha\|^2)
   \le 2^r$ (since $\|\alpha\| \le 1$ by `apssvT_e_integral_norm_le_one`).

This gives the *tighter* bound $\le 2^r$ (not $\le 2 \cdot 2^r$): the closure uses
`apssvBlockSum_j_T_indepFun` plus integral-linearity manipulations on the
deterministic split. -/
@[category API, AMS 11]
lemma apssvBlockSum_variance_eq (P r k : ℕ) (hk : 1 ≤ k) :
    ∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure =
      (2 : ℝ) ^ r *
        (1 - ‖∫ η, e ((k : ℝ) *
          apssvT η (fun _ : Fin r => false) P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖^2) := by
  -- (2) Pointwise complex identity for ‖B(η)‖² (norm_sq_split + cross_term_factor).
  have h_pw : ∀ η : List Bool → Bool,
      ((‖apssvBlockSum η P r k‖ ^ 2 : ℝ) : ℂ) =
      (2 : ℂ) ^ r +
      ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) *
        e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) := by
    intro η
    rw [apssvBlockSum_norm_sq_split η P r k]
    congr 1
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    exact apssvBlockSum_cross_term_factor η P r k w w'
  -- (3) Measurability and integrability of the cross-term summand.
  have h_continuous_e : Continuous e := by
    unfold e; exact Complex.continuous_exp.comp (by continuity)
  have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
  have h_meas_A : ∀ w w' : Fin r → Bool,
      Measurable (fun η : List Bool → Bool =>
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)) := by
    intro w w'
    refine h_continuous_e.measurable.comp ?_
    refine Measurable.div_const (Measurable.const_mul ?_ _) _
    exact (h_natCast_real.comp (apssvJ_measurable r w)).sub
          (h_natCast_real.comp (apssvJ_measurable r w'))
  have h_meas_B : ∀ w w' : Fin r → Bool,
      Measurable (fun η : List Bool → Bool =>
        e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r)) := by
    intro w w'
    refine h_continuous_e.measurable.comp ?_
    refine Measurable.div_const (Measurable.const_mul ?_ _) _
    exact (apssvT_measurable w P).sub (apssvT_measurable w' P)
  have h_int_AB : ∀ w w' : Fin r → Bool,
      MeasureTheory.Integrable (fun η : List Bool → Bool =>
        e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) *
        e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r))
        apssvEtaMeasure := fun w w' => by
    refine MeasureTheory.Integrable.of_bound
      ((h_meas_A w w').mul (h_meas_B w w')).aestronglyMeasurable 1 ?_
    refine MeasureTheory.ae_of_all _ fun η => ?_
    rw [norm_mul, norm_e, norm_e, mul_one]
  -- (4) Integrate both sides of h_pw, swapping ∫ with the finite double-sum.
  have h_int_eq : ((∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure : ℝ) : ℂ) =
      (2 : ℂ) ^ r +
      ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
        ∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) *
              e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r)
            ∂apssvEtaMeasure := by
    -- ((∫ ‖B‖² : ℝ) : ℂ) = ∫ ((‖B‖² : ℝ) : ℂ)
    rw [show ((∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure : ℝ) : ℂ) =
          ∫ η, ((‖apssvBlockSum η P r k‖^2 : ℝ) : ℂ) ∂apssvEtaMeasure from
        (integral_ofReal (𝕜 := ℂ) (f := fun η : List Bool → Bool =>
          ‖apssvBlockSum η P r k‖^2)).symm]
    -- Substitute pointwise identity.
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pw)]
    -- ∫ (2^r + cross) = ∫ 2^r + ∫ cross.
    have h_cross_integrable : MeasureTheory.Integrable
        (fun η : List Bool → Bool =>
          ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
            e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) *
            e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r))
        apssvEtaMeasure := by
      refine MeasureTheory.integrable_finset_sum _ fun w _ => ?_
      refine MeasureTheory.integrable_finset_sum _ fun w' _ => ?_
      exact h_int_AB w w'
    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _) h_cross_integrable]
    -- Constant integrates to (μ univ).toReal • c = 1 • 2^r = 2^r on probability measure.
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ (μ := apssvEtaMeasure),
        one_smul]
    congr 1
    -- Swap the outer ∫ with the outer ∑.
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl fun w _ => ?_
      -- Swap the inner ∫ with the inner ∑.
      exact MeasureTheory.integral_finset_sum _ fun w' _ => h_int_AB w w'
    · intro w _
      exact MeasureTheory.integrable_finset_sum _ fun w' _ => h_int_AB w w'
  -- (5) For each (w, w') with w ≠ w', apply j_T_indepFun to factor:
  --   ∫ A(w,w') · B(w,w') = (∫ A(w,w')) · (∫ B(w,w'))
  have h_AB_factor : ∀ w w' : Fin r → Bool,
      ∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r) *
              e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r) ∂apssvEtaMeasure =
      (∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
          ∂apssvEtaMeasure) *
      (∫ η, e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r)
          ∂apssvEtaMeasure) := by
    intro w w'
    exact (apssvBlockSum_j_T_indepFun w w' P k).integral_fun_mul_eq_mul_integral
      (h_meas_A w w').aestronglyMeasurable
      (h_meas_B w w').aestronglyMeasurable
  -- (6) Substitute h_AB_factor into the integral identity to get factored form.
  have h_int_factored : ((∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure : ℝ) : ℂ) =
      (2 : ℂ) ^ r +
      ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
        (∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
            ∂apssvEtaMeasure) *
        (∫ η, e ((k : ℝ) * (apssvT η w P - apssvT η w' P) / (2 : ℝ) ^ r)
            ∂apssvEtaMeasure) := by
    rw [h_int_eq]; congr 1
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => h_AB_factor w w'
  -- (7) Pick reference w₀ : Fin r → Bool (works for any r ≥ 0, vacuously when r = 0).
  let w₀ : Fin r → Bool := fun _ => false
  -- α := ∫ e(k T_{w₀}/2^r); β := ∫ e(-k T_{w₀}/2^r). Both are w-independent constants.
  set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure with hα_def
  set β : ℂ := ∫ η, e (-((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure with hβ_def
  -- (8) Substitute T-cross-term as α · β (via apssvBlockSum_T_diff_E_constant).
  have h_int_collapsed : ((∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure : ℝ) : ℂ) =
      (2 : ℂ) ^ r + (α * β) *
        ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
          ∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
            ∂apssvEtaMeasure := by
    rw [h_int_factored]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w' hw' => ?_
    have hww' : w ≠ w' :=
      Ne.symm (Finset.ne_of_mem_erase hw')
    rw [apssvBlockSum_T_diff_E_constant w w' w₀ hww' P k, ← hα_def, ← hβ_def]
    ring
  -- (9) Case split on whether 1 ≤ k % 2^r (use j-factor sum) or 2^r ∣ k (use bit-flip).
  by_cases hk_mod : 1 ≤ k % 2 ^ r
  · -- Case 1: 1 ≤ k % 2^r. Use apssv_j_factor_double_sum_mod for J_sum = -2^r.
    have h_int_A : ∀ w w' : Fin r → Bool,
        MeasureTheory.Integrable (fun η : List Bool → Bool =>
          e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r))
          apssvEtaMeasure := fun w w' => by
      refine MeasureTheory.Integrable.of_bound (h_meas_A w w').aestronglyMeasurable 1 ?_
      refine MeasureTheory.ae_of_all _ fun η => ?_
      rw [norm_e]
    -- Collapse ∑∑ ∫A = ∫ ∑∑ A = ∫ (-(2:ℂ)^r) = -(2:ℂ)^r.
    have h_j_sum : (∑ w : (Fin r → Bool),
        ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
          ∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
            ∂apssvEtaMeasure) = -(2 : ℂ) ^ r := by
      rw [show (∑ w : (Fin r → Bool),
                ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
                  ∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
                    ∂apssvEtaMeasure) =
              (∑ w : (Fin r → Bool),
                ∫ η, ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
                  e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
                    ∂apssvEtaMeasure) from
          Finset.sum_congr rfl fun w _ =>
            (MeasureTheory.integral_finset_sum _ fun w' _ => h_int_A w w').symm]
      rw [← MeasureTheory.integral_finset_sum _ fun w _ =>
            MeasureTheory.integrable_finset_sum _ fun w' _ => h_int_A w w']
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
            (fun η : List Bool → Bool => apssv_j_factor_double_sum_mod η r k hk_mod))]
      rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ (μ := apssvEtaMeasure),
          one_smul]
    -- Substitute h_j_sum into h_int_collapsed → 2^r · (1 - α·β).
    have h_int_final : ((∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure : ℝ) : ℂ) =
        (2 : ℂ) ^ r * (1 - α * β) := by
      rw [h_int_collapsed, h_j_sum]; ring
    -- α · β = ‖α‖² since β = conj(α).
    have hβ_eq : β = (starRingEnd ℂ) α := by
      rw [hβ_def, hα_def]
      have h_conj : ∀ η : List Bool → Bool,
          e (-((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r)) =
          (starRingEnd ℂ) (e ((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r)) := fun η => by
        rw [e_neg, ← conj_e]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_conj),
          integral_conj]
    have h_αβ_norm_sq : α * β = ((‖α‖^2 : ℝ) : ℂ) := by
      rw [hβ_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h_αβ_norm_sq] at h_int_final
    have h_real : (((2 : ℂ) ^ r * (1 - ((‖α‖^2 : ℝ) : ℂ)) : ℂ)) =
        ((((2 : ℝ) ^ r * (1 - ‖α‖^2)) : ℝ) : ℂ) := by push_cast; ring
    rw [h_real] at h_int_final
    have h_eq_real : ∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure =
        (2 : ℝ) ^ r * (1 - ‖α‖^2) := by exact_mod_cast h_int_final
    exact h_eq_real
  · -- Case 2: k % 2^r = 0, i.e. 2^r ∣ k. Use bit-flip symmetry to get α = 0.
    push_neg at hk_mod
    have hkdvd : 2 ^ r ∣ k :=
      Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨q, hq_eq⟩ := hkdvd
    have hq_pos : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq_pos
      · subst hq0; rw [Nat.mul_zero] at hq_eq; omega
      · exact hq_pos
    -- α = ∫ e(k·T/2^r) ∂η = ∫ e(q·T) ∂η [since k = 2^r · q] = 0 (by bit-flip symmetry).
    have hα_zero : α = 0 := by
      rw [hα_def]
      have h_eq_arg : ∀ η, ((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r) =
          (q : ℝ) * apssvT η w₀ P := by
        intro η
        have h_2pow_ne : ((2 : ℝ) ^ r : ℝ) ≠ 0 := by positivity
        have h_k_eq : (k : ℝ) = (2 : ℝ) ^ r * (q : ℝ) := by exact_mod_cast hq_eq
        rw [h_k_eq]; field_simp
      rw [show (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w₀ P / (2 : ℝ) ^ r)) =
            (fun η => e ((q : ℝ) * apssvT η w₀ P)) from funext fun η => by rw [h_eq_arg η]]
      exact apssvT_e_integral_q_eq_zero w₀ P q hq_pos
    -- α · β = 0.
    have hαβ : α * β = 0 := by rw [hα_zero]; ring
    rw [hαβ] at h_int_collapsed
    -- ((∫ ‖B‖²) : ℂ) = 2^r + 0 = 2^r.
    have h_real : ((((2 : ℝ) ^ r : ℝ) : ℂ)) = ((2 : ℂ) ^ r + 0 *
        ∑ w : (Fin r → Bool), ∑ w' ∈ (Finset.univ.erase w : Finset (Fin r → Bool)),
          ∫ η, e ((k : ℝ) * ((apssvJ η r w : ℝ) - (apssvJ η r w' : ℝ)) / (2 : ℝ) ^ r)
            ∂apssvEtaMeasure : ℂ) := by push_cast; ring
    rw [← h_real] at h_int_collapsed
    have h_eq_real : ∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure = (2 : ℝ) ^ r := by
      exact_mod_cast h_int_collapsed
    -- α = 0 ⟹ ‖α‖² = 0 ⟹ 2^r · (1 - 0) = 2^r matches h_eq_real.
    rw [h_eq_real, hα_zero, norm_zero]
    ring

/-- **Variance bound** (`≤ 2 · 2^r`): for any `k ≥ 1`,
$$ \mathbb{E}\big[\|B_{P, r}(k)\|^2\big] \le 2 \cdot 2^r. $$

Direct corollary of `apssvBlockSum_variance_eq` (the formula
`∫ ‖B‖² = 2^r · (1 - ‖α‖²)` with `α := ∫ e(k T_w₀/2^r)`) plus the trivial bounds
`‖α‖² ≥ 0` and `2^r ≥ 0`. The factor of `2` is loose: the equation actually
gives `≤ 2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_variance_bound (P r k : ℕ) (hk : 1 ≤ k) :
    ∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure ≤ 2 * (2 : ℝ) ^ r := by
  rw [apssvBlockSum_variance_eq P r k hk]
  have h_norm_nn : 0 ≤ ‖∫ η, e ((k : ℝ) * apssvT η (fun _ : Fin r => false) P /
      (2 : ℝ) ^ r) ∂apssvEtaMeasure‖^2 := by positivity
  have h_pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
  nlinarith

/-- **Variance bound, long-block regime** (Step 2 sharpening of [APSSV26b Prop 3.5]):
for any `k ≥ 1`,
$$ \mathbb{E}\big[\|B_{P, r}(k)\|^2\big] \le 4 \pi k. $$

Substituting `1 - ‖α‖² ≤ 4π·k/2^r` (from `apssvT_e_integral_one_sub_norm_sq_le`)
into the variance equation `∫ ‖B‖² = 2^r · (1 - ‖α‖²)` yields
`∫ ‖B‖² ≤ 2^r · 4π·k/2^r = 4π·k`. Strictly better than `2 · 2^r` whenever
`k ≤ 2^(r - 1)/π` — i.e., in the long-block regime `r ≥ b(k) + O(1)`. -/
@[category API, AMS 11]
lemma apssvBlockSum_variance_bound_long (P r k : ℕ) (hk : 1 ≤ k) :
    ∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure ≤
      4 * Real.pi * (k : ℝ) := by
  rw [apssvBlockSum_variance_eq P r k hk]
  have h_one_sub :=
    apssvT_e_integral_one_sub_norm_sq_le (fun _ : Fin r => false) P k r
  have h_pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
  have h_pow_ne : ((2 : ℝ) ^ r : ℝ) ≠ 0 := by positivity
  calc (2 : ℝ) ^ r * (1 - ‖∫ η, e ((k : ℝ) *
          apssvT η (fun _ : Fin r => false) P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖^2)
      ≤ (2 : ℝ) ^ r * (4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h_one_sub h_pow_nn
    _ = 4 * Real.pi * (k : ℝ) := by field_simp

/-- `η ↦ ‖apssvBlockSum η P r k‖²` is integrable: bounded by `4^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_sq_norm_integrable (P r k : ℕ) :
    MeasureTheory.Integrable
      (fun η : List Bool → Bool => ‖apssvBlockSum η P r k‖^2) apssvEtaMeasure := by
  have h_meas : Measurable (fun η : List Bool → Bool => ‖apssvBlockSum η P r k‖^2) :=
    (apssvBlockSum_measurable P r k).norm.pow_const 2
  refine MeasureTheory.Integrable.of_bound h_meas.aestronglyMeasurable ((4 : ℝ)^r) ?_
  apply MeasureTheory.ae_of_all
  intro η
  have h_nn : 0 ≤ ‖apssvBlockSum η P r k‖ := norm_nonneg _
  have h_le := apssvBlockSum_norm_le_two_pow η P r k
  have h_sq_le : ‖apssvBlockSum η P r k‖^2 ≤ ((2 : ℝ)^r)^2 :=
    pow_le_pow_left₀ h_nn h_le 2
  have h_4 : ((2 : ℝ)^r)^2 = (4 : ℝ)^r := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h_4] at h_sq_le
  rw [Real.norm_of_nonneg (by positivity)]
  exact h_sq_le

/-- **Variance bound, short-block regime (part of Step 5 of [APSSV26b Prop 3.5])**:
for `r ≤ b(k)`,
$$ \mathbb{E}\big[\|B_{P, r}(k)\|^2\big] \le 2 \cdot 4^{b - r/2} = 2 \cdot 2^{2b - r}. $$

In the "short-block" regime, the sum has fewer terms than the frequency scale,
and the bound scales by `4^{b-r/2}` instead of `2^r`. With the (now fully
general) `apssvBlockSum_variance_bound` providing `∫ ≤ 2·2^r` for any `k ≥ 1`,
this corollary follows immediately from `r ≤ b ⟹ r ≤ 2b − r ⟹ 2^r ≤ 2^(2b−r)`. -/
@[category API, AMS 11]
lemma apssvBlockSum_variance_bound_short (P r k : ℕ) (hk : 1 ≤ k) (hr : r ≤ apssvB k) :
    ∫ η, ‖apssvBlockSum η P r k‖^2 ∂apssvEtaMeasure ≤
      2 * (2 : ℝ) ^ (2 * apssvB k - r) := by
  -- The (now fully general) `apssvBlockSum_variance_bound` gives `∫ ≤ 2·2^r` for any
  -- `k ≥ 1`. Combined with `r ≤ b` ⟹ `r ≤ 2b − r` ⟹ `2^r ≤ 2^(2b−r)`, we conclude.
  have h_long := apssvBlockSum_variance_bound P r k hk
  have h_pow_le : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ (2 * apssvB k - r) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  linarith [h_pow_le, (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ r),
            (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * apssvB k - r))]

/- ## [APSSV26b Lemma 3.6] Finite residue reduction in `P`

The pointwise bound `‖B_{P, r}(k) - B_{P mod 2^h, r}(k)‖ ≤ 2π · k / 2^h`
allows replacing the universal-`P` quantification by a *finite* union over
residues `Q ∈ {0, …, 2^h - 1}`, at the cost of shifting the threshold by
`2π · k / 2^h`. This is what reduces the sub-Gaussian union bound from
"`∑'_P` (diverges)" to "`∑_{Q < 2^h}` (finite)". -/

/-- **`apssvPrefix` is invariant under `mod 2^h` for low indices**: if `ℓ ≤ h`
then `apssvPrefix (P mod 2^h) ℓ = apssvPrefix P ℓ`. The prefix uses bits at
positions `0, 1, …, ℓ−1`, all of which match between `P` and `P mod 2^h`. -/
@[category API, AMS 11]
lemma apssvPrefix_mod_eq_of_le {P h ℓ : ℕ} (hℓ : ℓ ≤ h) :
    apssvPrefix (P % 2 ^ h) ℓ = apssvPrefix P ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    have hℓh : ℓ < h := hℓ
    rw [apssvPrefix_succ, apssvPrefix_succ, ih (Nat.le_of_succ_le hℓ)]
    congr 1
    rw [Nat.testBit_mod_two_pow]
    simp [hℓh]

/-- The geometric tail `∑'_{ℓ ≥ h} (1/2)^(ℓ+1) = (1/2)^h`. -/
@[category API, AMS 11]
lemma apssv_geom_tail_eq (h : ℕ) :
    ∑' ℓ : ℕ, (if h ≤ ℓ then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0) = (1 / 2 : ℝ) ^ h := by
  -- Strategy: ∑'(if h ≤ ℓ then a_ℓ else 0) = ∑'_ℓ a_ℓ - ∑_{ℓ < h} a_ℓ.
  have h_summ_full : Summable (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1)) := by
    have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact hg.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  have h_summ_low : Summable
      (fun ℓ : ℕ => if ℓ < h then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) h_summ_full
    · by_cases hℓ : ℓ < h
      · simp only [if_pos hℓ]; positivity
      · simp only [if_neg hℓ]; exact le_refl 0
    · by_cases hℓ : ℓ < h
      · simp only [if_pos hℓ]; exact le_refl _
      · simp only [if_neg hℓ]; positivity
  -- Convert if-statement: (if h ≤ ℓ then a_ℓ else 0) = a_ℓ - (if ℓ < h then a_ℓ else 0).
  have h_split : (fun ℓ : ℕ => if h ≤ ℓ then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0) =
      (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1) -
        (if ℓ < h then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0)) := by
    funext ℓ
    by_cases hℓ : ℓ < h
    · simp only [if_pos hℓ, if_neg (Nat.not_le_of_lt hℓ)]; ring
    · simp only [if_neg hℓ, if_pos (Nat.le_of_not_lt hℓ)]; ring
  rw [h_split, Summable.tsum_sub h_summ_full h_summ_low]
  -- ∑' (1/2)^(ℓ+1) = 1.
  have h_full_tsum : ∑' ℓ : ℕ, ((1 / 2 : ℝ)) ^ (ℓ + 1) = 1 := by
    rw [show (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1)) =
        (fun ℓ => (1 / 2 : ℝ) * ((1 / 2 : ℝ)) ^ ℓ) from by funext ℓ; rw [pow_succ]; ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  -- ∑' (if ℓ < h then ...) = finite sum.
  have h_low_tsum : ∑' ℓ : ℕ, (if ℓ < h then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0) =
      ∑ ℓ ∈ Finset.range h, ((1 / 2 : ℝ)) ^ (ℓ + 1) := by
    rw [tsum_eq_sum (s := Finset.range h)]
    · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      rw [Finset.mem_range] at hℓ; rw [if_pos hℓ]
    · intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      rw [if_neg (by omega : ¬ ℓ < h)]
  have h_finite_sum : ∀ n : ℕ,
      ∑ ℓ ∈ Finset.range n, ((1 / 2 : ℝ)) ^ (ℓ + 1) = 1 - (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [h_full_tsum, h_low_tsum, h_finite_sum]
  ring

/-- **`apssvT` is approximately periodic in P with period `2^h`** (Lemma 3.6
of [APSSV26b §3.3], `T`-version): for any `w`, `η`, `P`, `h`,
$$ |T_{w, P} - T_{w, P \bmod 2^h}| \le 2^{-h}. $$

The terms of `apssvT` at positions `ℓ < h` coincide between `P` and `Q := P mod 2^h`
(both `P.testBit ℓ = Q.testBit ℓ` and `apssvPrefix P ℓ = apssvPrefix Q ℓ`), so the
difference is concentrated in the tail `ℓ ≥ h`, where each term has magnitude
`≤ 1/2^(ℓ+1)`. Termwise bound + `Summable.tsum_le_tsum`, then geometric tail. -/
@[category API, AMS 11]
lemma apssvT_residue_diff_bound {r : ℕ} (w : Fin r → Bool) (η : List Bool → Bool)
    (P h : ℕ) :
    |apssvT η w P - apssvT η w (P % 2 ^ h)| ≤ 1 / (2 : ℝ) ^ h := by
  -- Define the per-term function inline (no `set`).
  let f : ℕ → ℕ → ℝ := fun M ℓ =>
    (if (M.testBit ℓ).xor (η (apssvWordPrefix w r ++ apssvPrefix M ℓ)) then (1 : ℝ) else 0) /
      2 ^ (ℓ + 1)
  have h_T_eq : ∀ M, apssvT η w M = ∑' ℓ : ℕ, f M ℓ := fun _ => rfl
  have hf_nn : ∀ M ℓ, 0 ≤ f M ℓ := fun M ℓ => by show 0 ≤ _; positivity
  have hf_le : ∀ M ℓ, f M ℓ ≤ (1 / 2 : ℝ) ^ (ℓ + 1) := fun M ℓ => by
    show _ / _ ≤ _
    rw [div_pow, one_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    split_ifs <;> norm_num
  have h_eq_below : ∀ ℓ < h, f P ℓ = f (P % 2 ^ h) ℓ := fun ℓ hℓ => by
    have h_tb : P.testBit ℓ = (P % 2 ^ h).testBit ℓ := by
      rw [Nat.testBit_mod_two_pow]; simp [hℓ]
    have h_pref : apssvPrefix P ℓ = apssvPrefix (P % 2 ^ h) ℓ :=
      (apssvPrefix_mod_eq_of_le (Nat.le_of_lt hℓ)).symm
    show (if _ then _ else _) / _ = (if _ then _ else _) / _
    rw [h_tb, h_pref]
  have h_geom : Summable (fun ℓ : ℕ => ((1 / 2 : ℝ)) ^ (ℓ + 1)) := by
    have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact hg.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  have hf_summable : ∀ M, Summable (f M) := fun M =>
    Summable.of_nonneg_of_le (hf_nn M) (hf_le M) h_geom
  -- Bounding function g for diff.
  let g : ℕ → ℝ := fun ℓ => if h ≤ ℓ then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0
  have hg_nn : ∀ ℓ, 0 ≤ g ℓ := fun ℓ => by
    show 0 ≤ ite _ _ _
    by_cases hℓ : h ≤ ℓ
    · simp only [if_pos hℓ]; positivity
    · simp only [if_neg hℓ]; exact le_refl _
  have h_g_summable : Summable g := by
    refine Summable.of_nonneg_of_le hg_nn (fun ℓ => ?_) h_geom
    show ite _ _ _ ≤ _
    by_cases hℓ : h ≤ ℓ
    · simp only [if_pos hℓ]; exact le_refl _
    · simp only [if_neg hℓ]; positivity
  -- Termwise: |f P ℓ - f Q ℓ| ≤ g ℓ.
  have h_termwise : ∀ ℓ, |f P ℓ - f (P % 2 ^ h) ℓ| ≤ g ℓ := fun ℓ => by
    show _ ≤ ite _ _ _
    by_cases hℓ : h ≤ ℓ
    · simp only [if_pos hℓ]
      have h_lo : -((1 / 2 : ℝ)) ^ (ℓ + 1) ≤ f P ℓ - f (P % 2 ^ h) ℓ := by
        have h1 := hf_nn P ℓ; have h2 := hf_le (P % 2 ^ h) ℓ; linarith
      have h_hi : f P ℓ - f (P % 2 ^ h) ℓ ≤ ((1 / 2 : ℝ)) ^ (ℓ + 1) := by
        have h1 := hf_le P ℓ; have h2 := hf_nn (P % 2 ^ h) ℓ; linarith
      rw [abs_le]; exact ⟨h_lo, h_hi⟩
    · simp only [if_neg hℓ]
      rw [h_eq_below ℓ (Nat.lt_of_not_ge hℓ)]; simp
  rw [h_T_eq, h_T_eq]
  rw [← Summable.tsum_sub (hf_summable P) (hf_summable (P % 2 ^ h))]
  have h_diff_summable_norm : Summable (fun ℓ : ℕ => |f P ℓ - f (P % 2 ^ h) ℓ|) :=
    Summable.of_nonneg_of_le (fun ℓ => abs_nonneg _) h_termwise h_g_summable
  calc |∑' ℓ, (f P ℓ - f (P % 2 ^ h) ℓ)|
      = ‖∑' ℓ, (f P ℓ - f (P % 2 ^ h) ℓ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' ℓ, ‖f P ℓ - f (P % 2 ^ h) ℓ‖ := norm_tsum_le_tsum_norm h_diff_summable_norm
    _ ≤ ∑' ℓ, g ℓ := Summable.tsum_le_tsum
        (fun ℓ => by rw [Real.norm_eq_abs]; exact h_termwise ℓ)
        h_diff_summable_norm h_g_summable
    _ = 1 / (2 : ℝ) ^ h := by
        change ∑' ℓ : ℕ, (if h ≤ ℓ then ((1 / 2 : ℝ)) ^ (ℓ + 1) else 0) = _
        rw [apssv_geom_tail_eq, div_pow, one_pow]

/-- **Lemma 3.6 of [APSSV26b §3.3], `B`-version (finite residue reduction)**:
$$ \|B_{P, r}(k) - B_{P \bmod 2^h, r}(k)\| \le 2\pi \cdot k / 2^h. $$

The block sum depends on `P` only through finitely many low bits — combined with
the geometric residue bound on `apssvT`, the difference between `B_P` and
`B_Q` is controlled by `k/2^h`. This is the crucial reduction that lets the
universal-in-`P` `apssvBlockBound` predicate be checked over the *finite*
family of residue classes mod `2^h`. -/
@[category API, AMS 11]
lemma apssvBlockSum_residue_diff_bound (η : List Bool → Bool) (P r k h : ℕ) :
    ‖apssvBlockSum η P r k - apssvBlockSum η (P % 2 ^ h) r k‖ ≤
    2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by
  -- Per-summand bound: |e((k/2^r)(j_w + T_P)) - e((k/2^r)(j_w + T_Q))| ≤ 2π(k/2^r)·(1/2^h).
  have h_per_summand : ∀ w : Fin r → Bool,
      ‖e ((k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w P) / (2 : ℝ) ^ r) -
        e ((k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w (P % 2 ^ h)) / (2 : ℝ) ^ r)‖ ≤
      2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r * (1 / (2 : ℝ) ^ h) := by
    intro w
    set α : ℝ := (k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w P) / (2 : ℝ) ^ r
    set β : ℝ := (k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w (P % 2 ^ h)) / (2 : ℝ) ^ r
    -- ‖e α - e β‖ = ‖e β · (e (α - β) - 1)‖ = ‖e (α - β) - 1‖.
    have h_factor : e α - e β = e β * (e (α - β) - 1) := by
      rw [show α = β + (α - β) from by ring, e_add]
      ring_nf
    have h_norm : ‖e α - e β‖ = ‖e (α - β) - 1‖ := by
      rw [h_factor, norm_mul, norm_e, one_mul]
    rw [h_norm]
    -- ‖e t - 1‖ = 2·|sin(πt)| ≤ 2π·|t|.
    have h_e_bound : ‖e (α - β) - 1‖ ≤ 2 * Real.pi * |α - β| := by
      unfold e
      rw [show ((2 * Real.pi * (α - β) : ℝ) * Complex.I : ℂ) =
          Complex.I * ((2 * Real.pi * (α - β) : ℝ) : ℂ) from by ring]
      rw [Complex.norm_exp_I_mul_ofReal_sub_one]
      rw [Real.norm_eq_abs, show (2 * Real.pi * (α - β) / 2 : ℝ) = Real.pi * (α - β) from by
        ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc 2 * |Real.sin (Real.pi * (α - β))|
          ≤ 2 * |Real.pi * (α - β)| := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            exact Real.abs_sin_le_abs
        _ = 2 * Real.pi * |α - β| := by
            rw [abs_mul, abs_of_nonneg Real.pi_nonneg]; ring
    -- |α - β| = (k/2^r) · |T_P - T_Q|.
    have h_diff_eq : α - β =
        (k : ℝ) / (2 : ℝ) ^ r * (apssvT η w P - apssvT η w (P % 2 ^ h)) := by
      show (k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w P) / (2 : ℝ) ^ r -
           (k : ℝ) * ((apssvJ η r w : ℝ) + apssvT η w (P % 2 ^ h)) / (2 : ℝ) ^ r =
           (k : ℝ) / (2 : ℝ) ^ r * (apssvT η w P - apssvT η w (P % 2 ^ h))
      field_simp; ring
    have h_abs_diff : |α - β| ≤ (k : ℝ) / (2 : ℝ) ^ r * (1 / (2 : ℝ) ^ h) := by
      rw [h_diff_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2 ^ r)]
      exact mul_le_mul_of_nonneg_left
        (apssvT_residue_diff_bound w η P h)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2 ^ r)
    calc ‖e (α - β) - 1‖
        ≤ 2 * Real.pi * |α - β| := h_e_bound
      _ ≤ 2 * Real.pi * ((k : ℝ) / (2 : ℝ) ^ r * (1 / (2 : ℝ) ^ h)) :=
          mul_le_mul_of_nonneg_left h_abs_diff (by positivity)
      _ = 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r * (1 / (2 : ℝ) ^ h) := by ring
  -- Sum over 2^r summands.
  unfold apssvBlockSum
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun w _ => h_per_summand w)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  -- (2^r : ℕ) • (2π · k / 2^r · (1/2^h)) = 2π · k / 2^h.
  have h_compute : ((2 ^ r : ℕ) : ℝ) *
      (2 * Real.pi * (k : ℝ) / 2 ^ r * (1 / 2 ^ h)) = 2 * Real.pi * (k : ℝ) / 2 ^ h := by
    push_cast
    have : ((2 : ℝ) ^ r : ℝ) ≠ 0 := by positivity
    field_simp
  rw [h_compute]

/-- **Residue-reduction union bound** (key step toward eliminating the
universal-`P` quantification): the bad event for the universal-`P` block bound
is contained in the *finite* union over residue classes `Q < 2^h`.

For any threshold `τ` and reduction depth `h`, if `‖B_{P, r}(k)‖ > τ` for some
`P`, then by `apssvBlockSum_residue_diff_bound` we have
`‖B_{P mod 2^h, r}(k)‖ ≥ ‖B_{P, r}(k)‖ - 2π·k/2^h > τ - 2π·k/2^h`.
Since `Q := P mod 2^h ∈ {0, ..., 2^h − 1}`, the universal-`P` bad event
factors through the finite-`Q` union.

**Usage**: The right choice of `h` makes `2π·k/2^h ≤ τ/2`, reducing
`{∃ P, ‖B_P‖ > τ}` to `⋃ Q ∈ {0,...,2^h-1} {‖B_Q‖ > τ/2}`. The full union bound
then has at most `2^h` terms instead of infinitely many. -/
@[category API, AMS 11]
lemma apssvBlockSum_residue_union_bound (r k h : ℕ) (τ : ℝ) :
    {η : List Bool → Bool | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} ⊆
      ⋃ Q ∈ Finset.range (2 ^ h),
        {η : List Bool → Bool |
          τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h < ‖apssvBlockSum η Q r k‖} := by
  rintro η ⟨P, hP⟩
  have hQ_lt : P % 2 ^ h < 2 ^ h :=
    Nat.mod_lt P (pow_pos (by norm_num : (0 : ℕ) < 2) h)
  -- Reverse triangle: ‖B_P‖ - ‖B_{P mod 2^h}‖ ≤ ‖B_P - B_{P mod 2^h}‖.
  have h_diff := apssvBlockSum_residue_diff_bound η P r k h
  have h_revtri := abs_le.mp
    (abs_norm_sub_norm_le (apssvBlockSum η P r k) (apssvBlockSum η (P % 2 ^ h) r k))
  have h_BQ : τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h <
      ‖apssvBlockSum η (P % 2 ^ h) r k‖ := by
    linarith [h_revtri.1, h_revtri.2]
  -- Membership in ⋃ Q ∈ Finset.range (2^h), ...
  refine Set.mem_iUnion.mpr ⟨P % 2 ^ h, ?_⟩
  refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hQ_lt, ?_⟩
  exact h_BQ

/-- **Residue-reduction measure bound** (corollary of
`apssvBlockSum_residue_union_bound`): the measure of the universal-`P` bad
event is bounded by the sum of `2^h` "shifted" Markov terms.

Combined with `apssvBlockSum_concentration` or `apssvBlockSum_concentration_long`,
this gives a *finite* upper bound on the universal-`P` bad-event probability —
the key transformation that makes the union bound tractable in `(k, r)`.

The polynomial Markov tails from these concentration lemmas are summable in `r`
in either regime; with the sum over `Q` introducing a factor `≤ 2^h ≈ k/τ`,
the resulting bound is summable in `(k, r)` provided `τ` is chosen carefully
(per APSSV's choice `τ = C·√(r+b)·min(2^(r/2), 2^(b-r/2))`). -/
@[category API, AMS 11]
lemma apssvBlockSum_residue_measure_bound (r k h : ℕ) (τ : ℝ) :
    apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} ≤
      ∑ Q ∈ Finset.range (2 ^ h),
        apssvEtaMeasure {η | τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h <
          ‖apssvBlockSum η Q r k‖} := by
  refine le_trans (MeasureTheory.measure_mono
    (apssvBlockSum_residue_union_bound r k h τ)) ?_
  exact MeasureTheory.measure_biUnion_finset_le _ _

/- ## Concentration: trivial-bound shortcut, Markov tails, sub-Gaussian tails

Three flavours of tail bound on `‖apssvBlockSum‖`:

* **Trivial**: when `τ ≥ 2^r`, `‖B‖ ≤ 2^r ≤ τ` deterministically — the bad
  event is empty.
* **Markov**: `μ{‖B‖ ≥ t} ≤ Var/t² ≤ 2·2^r/t²` (or `≤ 4π·k/t²` long regime).
  Polynomial decay only, not tight enough for the union bound across all `(k, r, P)`.
* **Sub-Gaussian** (M=2 and linear; *deferred sorries*): `μ{‖B‖ ≥ t} ≤ 4·exp(...)`,
  the form needed for exp-summable tail across the (k, r) union. -/

/-- **Trivial-bound shortcut**: when the threshold `τ` exceeds the deterministic
bound `2^r` on `‖apssvBlockSum‖`, the bad event is empty.

Useful for handling the regime where the universal-`P` block bound holds
*deterministically* — no probabilistic estimate is needed when
`τ ≥ 2^r ≥ ‖B_{P, r}(k)‖` for all `η, P`. -/
@[category API, AMS 11]
lemma apssvBlockSum_bad_event_eq_empty_of_two_pow_le {r k : ℕ} (τ : ℝ)
    (hτ : (2 : ℝ) ^ r ≤ τ) :
    {η : List Bool → Bool | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} = ∅ := by
  ext η
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro P hP
  have h_triv := apssvBlockSum_norm_le_two_pow η P r k
  linarith

/-- **Centering of the random block sum (Step 4 of [APSSV26b Prop 3.5])**: for
every `k ≥ 1`,
$$ \mathbb{E}\big[\mathrm{apssvBlockSum}\,\eta\,P\,r\,k\big] = 0. $$

Linearity: `apssvBlockSum η P r k = ∑_{m < 2^r} e(k · apssvX η (P·2^r + m))` (by
`apssv_block_sum_eq`), and each summand has zero mean by `apssvX_integral_eq_zero`. -/
@[category API, AMS 11]
lemma apssvBlockSum_integral_eq_zero (P r k : ℕ) (hk : 1 ≤ k) :
    ∫ η, apssvBlockSum η P r k ∂apssvEtaMeasure = 0 := by
  -- Rewrite block sum as ∑ m < 2^r, e(k · apssvX η (P·2^r + m)).
  have h_eq : (fun η => apssvBlockSum η P r k) =
      fun η => ∑ m ∈ Finset.range (2 ^ r), e ((k : ℝ) * apssvX η (P * 2 ^ r + m)) := by
    funext η; exact (apssv_block_sum_eq η P r k).symm
  rw [h_eq]
  -- Linearity of the integral over a finite sum.
  rw [MeasureTheory.integral_finset_sum _ (fun m _ => apssvX_e_integrable (P * 2 ^ r + m) k)]
  -- Each integrand has zero mean.
  refine Finset.sum_eq_zero fun m _ => ?_
  exact apssvX_integral_eq_zero (P * 2 ^ r + m) k hk

/-- **Concentration consequence (Step 6 of [APSSV26b Prop 3.5])**: applying
Markov's inequality to `‖apssvBlockSum η P r k‖²` and using the variance bound
gives, for every `t > 0`,
$$ \mathbb{P}\big(\|B_{P, r}(k)\| \ge t\big) \le \frac{2 \cdot 2^r}{t^2}. $$

This is the Chebyshev-style consequence of the variance bound — sub-Gaussian
sharpening (replacing $1/t^2$ by $\exp(-t^2/c \cdot 2^r)$) requires a Hoeffding-type
argument, which is formalizable using `HasSubgaussianMGF` once the conditional
independence structure is in place. The polynomial bound stated here suffices
for the union bound across the *finite* parameter family $(k, P, r)$ in any
bounded range — the dyadic decomposition for fixed $N$ uses only $O(\log N)$
distinct levels $r$, so we don't need the full sub-Gaussian envelope. -/
@[category API, AMS 11]
lemma apssvBlockSum_concentration (P r k : ℕ) (hk : 1 ≤ k) (_hr : apssvB k ≤ r)
    (t : ℝ) (ht : 0 < t) :
    (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      2 * (2 : ℝ) ^ r / t^2 := by
  -- Squaring on nonneg values: {t ≤ ‖B‖} = {t² ≤ ‖B‖²}.
  have h_set_eq : {η : List Bool → Bool | t ≤ ‖apssvBlockSum η P r k‖} =
      {η | t^2 ≤ ‖apssvBlockSum η P r k‖^2} := by
    ext η
    have h_nn : 0 ≤ ‖apssvBlockSum η P r k‖ := norm_nonneg _
    refine ⟨fun h => pow_le_pow_left₀ ht.le h 2, fun h => ?_⟩
    -- From t² ≤ ‖B‖², t > 0, ‖B‖ ≥ 0: deduce t ≤ ‖B‖ via taking square roots.
    have h_sqrt := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq ht.le, Real.sqrt_sq h_nn] at h_sqrt
  rw [h_set_eq]
  -- Apply Markov: μ {η | t² ≤ ‖B‖²} ≤ E[‖B‖²]/t².
  have h_int := apssvBlockSum_sq_norm_integrable P r k
  have ht_sq_pos : (0 : ℝ) < t^2 := by positivity
  have h_meas_set : MeasurableSet {η : List Bool → Bool | t^2 ≤ ‖apssvBlockSum η P r k‖^2} := by
    have : Measurable (fun η : List Bool → Bool => ‖apssvBlockSum η P r k‖^2) :=
      (apssvBlockSum_measurable P r k).norm.pow_const 2
    exact measurableSet_le measurable_const this
  -- Use Integrable.measure_le_integral applied to f' = ‖B‖²/t².
  have h_scaled := (h_int.div_const (t^2)).measure_le_integral
    (μ := apssvEtaMeasure)
    (f_nonneg := MeasureTheory.ae_of_all _ (fun η => by positivity))
    (s := {η | t^2 ≤ ‖apssvBlockSum η P r k‖^2})
    (hs := fun η hη => by
      rw [le_div_iff₀ ht_sq_pos, one_mul]; exact hη)
  -- Bound by the variance (no longer requires deriving k < 2^r — variance_bound now
  -- handles all k ≥ 1).
  have h_var := apssvBlockSum_variance_bound P r k hk
  have h_int_div : ∫ η, ‖apssvBlockSum η P r k‖^2 / t^2 ∂apssvEtaMeasure ≤ 2 * (2 : ℝ)^r / t^2 := by
    rw [MeasureTheory.integral_div]; exact div_le_div_of_nonneg_right h_var ht_sq_pos.le
  have h_ofReal_le : ENNReal.ofReal (∫ η, ‖apssvBlockSum η P r k‖^2 / t^2 ∂apssvEtaMeasure) ≤
      ENNReal.ofReal (2 * (2 : ℝ)^r / t^2) := ENNReal.ofReal_le_ofReal h_int_div
  have h_chain : apssvEtaMeasure {η | t^2 ≤ ‖apssvBlockSum η P r k‖^2} ≤
      ENNReal.ofReal (2 * (2 : ℝ)^r / t^2) := h_scaled.trans h_ofReal_le
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ)^r := by positivity
  have h_rhs_nn : (0 : ℝ) ≤ 2 * (2 : ℝ)^r / t^2 := by positivity
  rw [show (2 * (2 : ℝ)^r / t^2 : ℝ) = ((ENNReal.ofReal (2 * (2 : ℝ)^r / t^2)).toReal) from
        (ENNReal.toReal_ofReal h_rhs_nn).symm]
  exact ENNReal.toReal_mono (by finiteness) h_chain

/-- **Long-regime concentration** (sharper Markov via the linear-in-`k` variance):
for any `t > 0`,
$$ \mathbb{P}\big(\|B_{P, r}(k)\| \ge t\big) \le \frac{4 \pi k}{t^2}. $$

Strictly tighter than `apssvBlockSum_concentration` whenever `2 \pi k \le 2^r`,
i.e., in the long-block regime `k \ll 2^r`. This is the `1/t^2` Markov form of
the linear-in-`k` variance `apssvBlockSum_variance_bound_long`.

The Bernstein/sub-Gaussian sharpening (replacing the polynomial tail by
`exp(-t^2/(c \cdot k))`) is what's needed for the union bound across the
universal-`P` quantification in `apssvBlockBound`; that requires either Mathlib's
`HasSubgaussianMGF` chassis or a custom MGF argument. -/
@[category API, AMS 11]
lemma apssvBlockSum_concentration_long (P r k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) :
    (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      4 * Real.pi * (k : ℝ) / t^2 := by
  -- Squaring on nonneg values: {t ≤ ‖B‖} = {t² ≤ ‖B‖²}.
  have h_set_eq : {η : List Bool → Bool | t ≤ ‖apssvBlockSum η P r k‖} =
      {η | t^2 ≤ ‖apssvBlockSum η P r k‖^2} := by
    ext η
    have h_nn : 0 ≤ ‖apssvBlockSum η P r k‖ := norm_nonneg _
    refine ⟨fun h => pow_le_pow_left₀ ht.le h 2, fun h => ?_⟩
    have h_sqrt := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq ht.le, Real.sqrt_sq h_nn] at h_sqrt
  rw [h_set_eq]
  have h_int := apssvBlockSum_sq_norm_integrable P r k
  have ht_sq_pos : (0 : ℝ) < t^2 := by positivity
  have h_meas_set : MeasurableSet {η : List Bool → Bool |
      t^2 ≤ ‖apssvBlockSum η P r k‖^2} := by
    have : Measurable (fun η : List Bool → Bool => ‖apssvBlockSum η P r k‖^2) :=
      (apssvBlockSum_measurable P r k).norm.pow_const 2
    exact measurableSet_le measurable_const this
  have h_scaled := (h_int.div_const (t^2)).measure_le_integral
    (μ := apssvEtaMeasure)
    (f_nonneg := MeasureTheory.ae_of_all _ (fun η => by positivity))
    (s := {η | t^2 ≤ ‖apssvBlockSum η P r k‖^2})
    (hs := fun η hη => by rw [le_div_iff₀ ht_sq_pos, one_mul]; exact hη)
  have h_var := apssvBlockSum_variance_bound_long P r k hk
  have h_int_div : ∫ η, ‖apssvBlockSum η P r k‖^2 / t^2 ∂apssvEtaMeasure ≤
      4 * Real.pi * (k : ℝ) / t^2 := by
    rw [MeasureTheory.integral_div]; exact div_le_div_of_nonneg_right h_var ht_sq_pos.le
  have h_ofReal_le : ENNReal.ofReal
      (∫ η, ‖apssvBlockSum η P r k‖^2 / t^2 ∂apssvEtaMeasure) ≤
      ENNReal.ofReal (4 * Real.pi * (k : ℝ) / t^2) :=
    ENNReal.ofReal_le_ofReal h_int_div
  have h_chain : apssvEtaMeasure {η | t^2 ≤ ‖apssvBlockSum η P r k‖^2} ≤
      ENNReal.ofReal (4 * Real.pi * (k : ℝ) / t^2) := h_scaled.trans h_ofReal_le
  have h_rhs_nn : (0 : ℝ) ≤ 4 * Real.pi * (k : ℝ) / t^2 := by positivity
  rw [show (4 * Real.pi * (k : ℝ) / t^2 : ℝ) =
        ((ENNReal.ofReal (4 * Real.pi * (k : ℝ) / t^2)).toReal) from
        (ENNReal.toReal_ofReal h_rhs_nn).symm]
  exact ENNReal.toReal_mono (by finiteness) h_chain

/-- **Pointwise per-summand `|Re| ≤ 1`**: for any `η, P, r, k, w`, the real part
of the per-`w` factored summand `c_w · Y_w := e(k j_r(w)/2^r) · e(k T_w/2^r)`
has absolute value at most `1`. (Both factors have unit modulus, so the
product does too.) -/
@[category API, AMS 11]
lemma apssvBlockSum_re_factored_summand_abs_le_one (η : List Bool → Bool)
    (P r k : ℕ) (w : Fin r → Bool) :
    |(e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
        e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re| ≤ 1 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_e, norm_e, mul_one]

/-- **Pointwise per-summand `|Im| ≤ 1`**: imaginary-part analog of
`apssvBlockSum_re_factored_summand_abs_le_one`. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_factored_summand_abs_le_one (η : List Bool → Bool)
    (P r k : ℕ) (w : Fin r → Bool) :
    |(e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
        e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im| ≤ 1 := by
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, norm_e, norm_e, mul_one]

/-- **Real-part decomposition**: `Re(B(η)) = ∑_w Re(c_w(η) · Y_w(η))`. Direct
application of `Complex.re` (which distributes over finite sums) to
`apssvBlockSum_eq_sum_factored`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_eq_sum_factored (η : List Bool → Bool) (P r k : ℕ) :
    (apssvBlockSum η P r k).re =
      ∑ w : Fin r → Bool,
        (e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re := by
  rw [apssvBlockSum_eq_sum_factored, Complex.re_sum]

/-- **Imaginary-part decomposition**: `Im(B(η)) = ∑_w Im(c_w(η) · Y_w(η))`. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_eq_sum_factored (η : List Bool → Bool) (P r k : ℕ) :
    (apssvBlockSum η P r k).im =
      ∑ w : Fin r → Bool,
        (e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im := by
  rw [apssvBlockSum_eq_sum_factored, Complex.im_sum]

/-- **Centered real-part decomposition**: for `1 ≤ k`,
`Re(B(η)) = ∑_w Re(c_w(η) · (Y_w(η) - α))` where `α := E[Y_{w₀}]` is the
common Fourier expectation (constant in `w` by `apssvT_e_integral_w_invariant`).

Combines `apssvBlockSum_eq_centered_sum` with `Complex.re_sum`. The form is
ready for Hoeffding's lemma per-`w` since each summand `Re(c_w · (Y_w - α))`
has `|·| ≤ 2` and conditional mean zero (given the short-prefix σ-algebra). -/
@[category API, AMS 11]
lemma apssvBlockSum_re_eq_centered_sum {r : ℕ} (η : List Bool → Bool)
    (P k : ℕ) (hk : 1 ≤ k) (w₀ : Fin r → Bool) :
    (apssvBlockSum η P r k).re =
      ∑ w : Fin r → Bool,
        (e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re := by
  rw [apssvBlockSum_eq_centered_sum η P k hk w₀, Complex.re_sum]

/-- **Centered imaginary-part decomposition**: imaginary-part analog of
`apssvBlockSum_re_eq_centered_sum`. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_eq_centered_sum {r : ℕ} (η : List Bool → Bool)
    (P k : ℕ) (hk : 1 ≤ k) (w₀ : Fin r → Bool) :
    (apssvBlockSum η P r k).im =
      ∑ w : Fin r → Bool,
        (e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im := by
  rw [apssvBlockSum_eq_centered_sum η P k hk w₀, Complex.im_sum]

/-- **Pointwise centered-summand bound `|·| ≤ 2`**: each centered summand
`c_w(η) · (Y_w(η) - α)` has norm at most `2`. (Trivial bound: `|c_w| = 1` and
`|Y_w - α| ≤ |Y_w| + |α| ≤ 1 + 1 = 2`.) Same statement extracted from
`apssvBlockSum_centered_summand_norm_bound`'s proof, but as the M=2 bound
(without the linear-`k` improvement). -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_summand_norm_le_two {r : ℕ} (η : List Bool → Bool)
    (P k : ℕ) (w w₀ : Fin r → Bool) :
    ‖e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)‖ ≤ 2 := by
  rw [norm_mul, norm_e, one_mul]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)‖ = 1 := norm_e _
  have h2 : ‖∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure‖ ≤ 1 :=
    apssvT_e_integral_norm_le_one w₀ P k r
  linarith

/-- **Pointwise bound on Re B**: `|Re B| ≤ 2^r`. Follows from
`apssvBlockSum_norm_le_two_pow` + `Complex.abs_re_le_norm`. Useful as a
bounded-r.v. step toward integrability of `exp(t · Re B)`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_abs_le (η : List Bool → Bool) (P r k : ℕ) :
    |(apssvBlockSum η P r k).re| ≤ (2 : ℝ) ^ r :=
  (Complex.abs_re_le_norm _).trans (apssvBlockSum_norm_le_two_pow η P r k)

/-- **Pointwise bound on Im B**: `|Im B| ≤ 2^r`. Imaginary analog of
`apssvBlockSum_re_abs_le`. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_abs_le (η : List Bool → Bool) (P r k : ℕ) :
    |(apssvBlockSum η P r k).im| ≤ (2 : ℝ) ^ r :=
  (Complex.abs_im_le_norm _).trans (apssvBlockSum_norm_le_two_pow η P r k)

/-- **Measurability of Re B**: `η ↦ (apssvBlockSum η P r k).re` is measurable.
Composes `apssvBlockSum_measurable` with `Complex.measurable_re`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_measurable (P r k : ℕ) :
    Measurable (fun η : List Bool → Bool => (apssvBlockSum η P r k).re) :=
  Complex.measurable_re.comp (apssvBlockSum_measurable P r k)

/-- **Measurability of Im B**: imaginary analog. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_measurable (P r k : ℕ) :
    Measurable (fun η : List Bool → Bool => (apssvBlockSum η P r k).im) :=
  Complex.measurable_im.comp (apssvBlockSum_measurable P r k)

/-- **Integrability of `exp(t · Re B)`**: since `|Re B| ≤ 2^r` deterministically,
`exp(t · Re B)` is bounded by `exp(|t| · 2^r)`. On a probability measure
(`apssvEtaMeasure`), bounded measurable functions are integrable. This is the
"easy" half of `HasSubgaussianMGF`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_integrable_exp_mul (P r k : ℕ) (t : ℝ) :
    MeasureTheory.Integrable
      (fun η : List Bool → Bool => Real.exp (t * (apssvBlockSum η P r k).re))
      apssvEtaMeasure := by
  have h_meas : Measurable
      (fun η : List Bool → Bool => Real.exp (t * (apssvBlockSum η P r k).re)) :=
    Real.measurable_exp.comp ((apssvBlockSum_re_measurable P r k).const_mul t)
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const
      (Real.exp (|t| * (2 : ℝ) ^ r)))
    h_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
  intro η
  have h_abs : |(apssvBlockSum η P r k).re| ≤ (2 : ℝ) ^ r :=
    apssvBlockSum_re_abs_le η P r k
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have h_2pow_pos : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
  have h_t_re_le : t * (apssvBlockSum η P r k).re ≤ |t| * (2 : ℝ) ^ r := by
    have h1 : t * (apssvBlockSum η P r k).re ≤
        |t * (apssvBlockSum η P r k).re| := le_abs_self _
    rw [abs_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h_abs (abs_nonneg _)
  exact h_t_re_le

/-- **Integrability of `exp(t · Im B)`**: imaginary analog. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_integrable_exp_mul (P r k : ℕ) (t : ℝ) :
    MeasureTheory.Integrable
      (fun η : List Bool → Bool => Real.exp (t * (apssvBlockSum η P r k).im))
      apssvEtaMeasure := by
  have h_meas : Measurable
      (fun η : List Bool → Bool => Real.exp (t * (apssvBlockSum η P r k).im)) :=
    Real.measurable_exp.comp ((apssvBlockSum_im_measurable P r k).const_mul t)
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const
      (Real.exp (|t| * (2 : ℝ) ^ r)))
    h_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
  intro η
  have h_abs : |(apssvBlockSum η P r k).im| ≤ (2 : ℝ) ^ r :=
    apssvBlockSum_im_abs_le η P r k
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have h_t_im_le : t * (apssvBlockSum η P r k).im ≤ |t| * (2 : ℝ) ^ r := by
    have h1 : t * (apssvBlockSum η P r k).im ≤
        |t * (apssvBlockSum η P r k).im| := le_abs_self _
    rw [abs_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h_abs (abs_nonneg _)
  exact h_t_im_le

/- ## Conditional sub-Gaussian MGF chassis: two formalization paths

The MGF bound `mgf(Re B) μ t ≤ exp(2^r · t²/2)` (and the linear analog) is the
heart of [APSSV26b §3 Prop 3.5]. The paper's argument:

> "Conditional on the values of `(η_c)_{|c| < r}`, the variables `Y_w` are
> independent. By Hoeffding's lemma applied fiber-wise, the conditional MGF of
> `Re B = ∑_w Re(c_w · Y_w)` at `t` is bounded by `exp(2^r · t²/2 + t · Re(α · J_sum))`.
> Using the deterministic vanishing `α · J_sum = 0` (`apssv_alpha_J_sum_eq_zero`),
> this gives the unconditional bound `mgf(Re B) ≤ exp(2^r · t²/2)`."

Two formalization paths exist for this argument:

### Path A (paper-aligned, chassis-based) — ACTIVE

Uses `ProbabilityTheory.HasCondSubgaussianMGF` (Mathlib `Probability/Moments/SubGaussian.lean`)
which is defined as `Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)`.

Phases:
- **Phase 1-3 [DONE]**: Define `apssvShortSigma r`, `apssvLongSigma r`; prove
  measurability of `c_w`, `Y_w`, `apssvJ`, `apssvT` wrt them; prove
  `Indep apssvShortSigma apssvLongSigma μ` (`apssv_short_long_indep`); prove
  `IndepFun c_w Y_w μ` per-`w` (`apssv_c_Y_indepFun`).
- **Phase A** (this section): build `HasCondSubgaussianMGF apssvShortSigma _
  (η ↦ Re(c_w · (Y_w - α))) 1 μ` per-`w`. This requires showing that, for
  `(μ.trim hm)`-a.e. `ω'`, under `condExpKernel μ apssvShortSigma ω'`:
    1. `c_w(η) = c_w(ω')` a.s. (from `apssvBlockSum_c_apssvShortSigma_measurable`)
    2. `Y_w` retains its unconditional law (from `apssv_short_long_indep` +
       `condExp_indep_eq` style fact: σ-long-measurable functions are unaffected
       by conditioning on σ-short)
    3. Reduce mgf computation to unconditional Hoeffding on
       `Re(z_w · (Y_w - α)) ∈ [Re(z_w · α) ± 1]` (range 2, mean 0, σ² = 1)
- **Phase B**: sum aggregator. Mathlib has `HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF`
  for *martingales* (filtration); we'd specialize to the constant filtration
  `ℱ_i = apssvShortSigma r` for all `i`, OR build a direct conditional analog of
  `HasSubgaussianMGF.sum_of_iIndepFun` for `iCondIndepFun`.
- **Phase C**: tower lift via `HasSubgaussianMGF_add_of_HasCondSubgaussianMGF`
  (with `X = 0`, `cX = 0`).
- **Phase D**: linear bound (`16π²k²/2^r`) — parallel to A-C using the sharper
  per-summand bound `|c_w · (Y_w - α)| ≤ 2π·k/2^r` from
  `apssvBlockSum_centered_summand_norm_bound`.

### Path B (alternative, Fubini-based) — DOCUMENTED, NOT TAKEN

Avoids the `condExpKernel` chassis entirely by working at the level of explicit
integrals:

1. **Measure splitting**: build a `MeasurableEquiv (List Bool → Bool) ≃
   ({c // c.length < r} → Bool) × ({c // r ≤ c.length} → Bool)` via
   `Equiv.piSum` after partitioning `List Bool ≃ Short ⊕ Long`.
   Push `apssvEtaMeasure` through to get
   `apssvEtaMeasure = (μ_short × μ_long).map equiv⁻¹` where `μ_short`, `μ_long`
   are `infinitePi`s over the respective subtypes.
2. **Fubini**: `∫ exp(t · Re B) dη = ∫_short ∫_long exp(t · Re B(η_short, η_long))
   dη_long dη_short`.
3. **Inner integral, fixed `η_short`**: the `(Y_w)_w` family is iIndepFun under
   `μ_long` (each `Y_w` depends on a disjoint subset of long coords). Apply
   `HasSubgaussianMGF.sum_of_iIndepFun` directly (no chassis needed!) — Mathlib
   has this lemma. Each per-`w` term has param 1 by Hoeffding on `Re(z_w · Y_w)
   ∈ [-1, 1]` with mean `Re(z_w · α)`. Sum gives param `2^r` and linear term
   `t · Re(α · ∑_w z_w) = t · Re(α · J_sum(η_short))`.
4. **Outer integral**: the inner result is `exp(2^r · t²/2 + t · Re(α · J_sum(η_short)))`,
   a deterministic function of `η_short`. Using `apssv_alpha_J_sum_eq_zero`,
   `α · J_sum(η_short) = 0` everywhere, so the bound is `exp(2^r · t²/2)`,
   independent of `η_short`. Integrating against `μ_short` preserves the constant.

**Trade-offs**:
- Path A directly mirrors the paper's *language* (conditional MGF, Hoeffding
  fiber-wise) but requires building Mathlib infrastructure (the conditional
  sum aggregator in Phase B is the main missing piece).
- Path B avoids the chassis but requires building the measure-splitting
  `MeasurableEquiv` (Phase 1) which is its own ~100-200 line subproject.
  Once that's done, Phases 2-4 use Mathlib's existing `iIndepFun.integral_fun_prod_comp`,
  `HasSubgaussianMGF.sum_of_iIndepFun`, and basic `Fubini`. The Phase B sum
  aggregator from Path A is *not* needed.

This file pursues Path A (paper-aligned). -/

/- ## Reusable conditional-kernel helpers (Mathlib upstream candidates)

The three helpers below abstract the structural facts about `condExpKernel`
needed to compute the per-`w` conditional MGF. They are stated in full
generality (no APSSV dependencies) and could be contributed to Mathlib's
`Probability/Kernel/Condexp.lean` upstream.

We open `MeasureTheory` and `ProbabilityTheory` locally for cleaner notation. -/

section CondExpKernelHelpers

open MeasureTheory ProbabilityTheory

/-- **Mathlib upstream candidate**: For an `m`-strongly-measurable real-valued
bounded function `f`, the conditional kernel `condExpKernel μ m ω'` puts all
its mass on the m-atom containing `ω'`, so `f` is `condExpKernel μ m ω'`-a.s.
equal to `f ω'` for `μ.trim hm`-a.e. `ω'`.

**Proof strategy**: applying `condExp_ae_eq_trim_integral_condExpKernel` and
`condExp_of_stronglyMeasurable` to both `f` and `f^2` gives
`∫ f d κ(ω') = f(ω')` and `∫ f² d κ(ω') = f(ω')²` for a.e. `ω'`. Combining,
`∫ (f - f(ω'))² d κ(ω') = 0`, hence `f =ᵐ[κ(ω')] (fun _ ↦ f ω')`.

The boundedness assumption simplifies the proof by giving uniform integrability
of `f`, `f²`, `(f-c)²` under any probability measure; integrability of `f²`
under each fiber `κ(ω')` then follows automatically.

TODO: Mathlib upstream candidate. -/
@[category API, AMS 11]
lemma condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {f : Ω → ℝ} {C : ℝ}
    (hf_meas : StronglyMeasurable[m] f)
    (hf_bd : ∀ ω, |f ω| ≤ C) :
    ∀ᵐ ω' ∂(μ.trim hm),
      f =ᵐ[condExpKernel μ m ω'] (fun _ => f ω') := by
  -- Top-level measurability and integrability from boundedness.
  have hf_meas_top : Measurable f := (hf_meas.measurable).mono hm le_rfl
  have hf_aestrong : AEStronglyMeasurable f μ := hf_meas_top.aestronglyMeasurable
  have hf_int : Integrable f μ :=
    Integrable.of_bound hf_aestrong C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hf_bd ω))
  have h_f_sq_meas : StronglyMeasurable[m] (fun ω => (f ω) ^ 2) := hf_meas.pow 2
  have h_f_sq_meas_top : Measurable (fun ω => (f ω) ^ 2) := hf_meas_top.pow_const 2
  -- f² ≤ C² so f² is integrable.
  have hf_sq_int : Integrable (fun ω => (f ω) ^ 2) μ := by
    refine Integrable.mono' (g := fun _ => C ^ 2) (integrable_const _)
      h_f_sq_meas_top.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h_abs := hf_bd ω
    nlinarith [sq_nonneg (|f ω| - C), abs_nonneg (f ω), sq_abs (f ω)]
  -- Step 1: ∫ f dκ(ω') = f(ω') for (μ.trim hm)-a.e. ω'.
  -- condExp_ae_eq_trim_integral_condExpKernel: μ[f|m] =ᵐ[μ.trim hm] (fun ω' ↦ ∫ f dκ(ω')).
  -- condExp_of_stronglyMeasurable: μ[f|m] = f.
  have h_int_f : ∀ᵐ ω' ∂(μ.trim hm), ∫ y, f y ∂(condExpKernel μ m ω') = f ω' := by
    have h1 := condExp_ae_eq_trim_integral_condExpKernel hm hf_int
    have h2 : μ[f|m] = f := condExp_of_stronglyMeasurable hm hf_meas hf_int
    have h3 : (fun ω => ∫ y, f y ∂(condExpKernel μ m ω)) =ᵐ[μ.trim hm] f := by
      filter_upwards [h1] with ω hω; rw [← hω, h2]
    filter_upwards [h3] with ω' hω'; exact hω'
  -- Step 2: ∫ f² dκ(ω') = f(ω')² for (μ.trim hm)-a.e. ω'.
  have h_int_f_sq : ∀ᵐ ω' ∂(μ.trim hm),
      ∫ y, (f y) ^ 2 ∂(condExpKernel μ m ω') = (f ω') ^ 2 := by
    have h1 := condExp_ae_eq_trim_integral_condExpKernel hm hf_sq_int
    have h2 : μ[fun ω => (f ω) ^ 2|m] = (fun ω => (f ω) ^ 2) :=
      condExp_of_stronglyMeasurable hm h_f_sq_meas hf_sq_int
    have h3 : (fun ω => ∫ y, (f y) ^ 2 ∂(condExpKernel μ m ω)) =ᵐ[μ.trim hm]
        (fun ω => (f ω) ^ 2) := by
      filter_upwards [h1] with ω hω; rw [← hω, h2]
    filter_upwards [h3] with ω' hω'; exact hω'
  -- Step 3: combine to show ∫ (f - f(ω'))² dκ(ω') = 0 for a.e. ω'.
  -- Each fiber κ(ω') is a probability measure (IsMarkovKernel condExpKernel).
  -- We get fiber integrability of f directly from boundedness.
  filter_upwards [h_int_f, h_int_f_sq] with ω' h_f_eq h_f_sq_eq
  have h_f_int_fiber : Integrable f (condExpKernel μ m ω') := by
    refine Integrable.mono' (g := fun _ => C) (integrable_const _)
      hf_meas_top.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs]; exact hf_bd y
  -- Goal: f =ᵐ[κ(ω')] (fun _ => f ω')
  -- Show: ∫ (f - f(ω'))² dκ(ω') = 0
  have h_sq_eq_zero :
      ∫ y, (f y - f ω') ^ 2 ∂(condExpKernel μ m ω') = 0 := by
    have h_expand : ∀ y, (f y - f ω') ^ 2 = (f y) ^ 2 - 2 * (f ω') * f y + (f ω') ^ 2 := by
      intro y; ring
    -- Decompose the integral.
    have h_sq_int_fiber : Integrable (fun y => (f y) ^ 2) (condExpKernel μ m ω') := by
      refine Integrable.mono' (g := fun _ => C ^ 2) (integrable_const _)
        h_f_sq_meas_top.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (f y), abs_nonneg (f y), hf_bd y, sq_nonneg (|f y| - C)]
    have h_const_int : Integrable (fun _ : Ω => (f ω') ^ 2) (condExpKernel μ m ω') :=
      integrable_const _
    have h_lin_int : Integrable (fun y => 2 * (f ω') * f y) (condExpKernel μ m ω') :=
      h_f_int_fiber.const_mul (2 * f ω')
    have h_diff_int : Integrable (fun y => (f y) ^ 2 - 2 * (f ω') * f y)
        (condExpKernel μ m ω') := h_sq_int_fiber.sub h_lin_int
    rw [show (fun y => (f y - f ω') ^ 2) =
        (fun y => (f y) ^ 2 - 2 * (f ω') * f y + (f ω') ^ 2) from funext h_expand]
    rw [integral_add h_diff_int h_const_int,
        integral_sub h_sq_int_fiber h_lin_int,
        integral_const, MeasureTheory.integral_const_mul]
    -- Each fiber is a probability measure (Markov kernel).
    have h_prob : IsProbabilityMeasure (condExpKernel μ m ω') :=
      IsMarkovKernel.isProbabilityMeasure (κ := condExpKernel μ m) ω'
    rw [h_f_sq_eq, h_f_eq]
    have h_univ : ((condExpKernel μ m ω').real Set.univ) = 1 := by
      simp [MeasureTheory.measureReal_def, measure_univ]
    simp [h_univ]; ring
  -- ∫ (f - f(ω'))² dκ(ω') = 0 + (f - f(ω'))² ≥ 0 ⟹ (f - f(ω'))² = 0 a.e. ⟹ f = f(ω') a.e.
  have h_sq_int_fiber : Integrable (fun y => (f y - f ω') ^ 2) (condExpKernel μ m ω') := by
    have h_meas : Measurable (fun y => (f y - f ω') ^ 2) :=
      (hf_meas_top.sub_const _).pow_const 2
    refine Integrable.mono' (g := fun _ => (2 * C) ^ 2) (integrable_const _)
      h_meas.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |f y - f ω'| ≤ 2 * C := by
      have h2 : |f y - f ω'| ≤ |f y| + |f ω'| := abs_sub _ _
      linarith [hf_bd y, hf_bd ω']
    nlinarith [abs_nonneg (f y - f ω'), sq_abs (f y - f ω')]
  have h_sq_ae_zero :
      (fun y => (f y - f ω') ^ 2) =ᵐ[condExpKernel μ m ω'] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) h_sq_int_fiber).mp h_sq_eq_zero
  filter_upwards [h_sq_ae_zero] with y hy
  -- (f y - f ω')^2 = 0 ⟹ f y = f ω'
  have : f y - f ω' = 0 := by
    have : (f y - f ω') ^ 2 = 0 := hy
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- **Mathlib upstream candidate**: If `m` and `m'` are independent σ-algebras
under `μ`, and `f` is `m'`-strongly-measurable and integrable, then under the
conditional kernel `condExpKernel μ m ω'`, the integral of `f` equals the
unconditional integral `∫ f ∂μ` for `μ.trim hm`-almost every `ω'`.

**Proof strategy**:
- `condExp_indep_eq`: `μ[f|m] =ᵐ[μ] (fun _ ↦ ∫ f ∂μ)`.
- Lift to trim via `ae_eq_trim_of_stronglyMeasurable` (both sides are `m`-meas).
- Combine with `condExp_ae_eq_trim_integral_condExpKernel`:
  `μ[f|m] =ᵐ[μ.trim hm] (fun ω' ↦ ∫ f d(condExpKernel μ m ω'))`.

TODO: Mathlib upstream candidate. -/
@[category API, AMS 11]
lemma integral_condExpKernel_of_indep
    {Ω : Type*} {m m' mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) (hm' : m' ≤ mΩ)
    (h_indep : Indep m' m μ)
    {f : Ω → ℝ} (hf_meas : StronglyMeasurable[m'] f)
    (hf_int : Integrable f μ) :
    ∀ᵐ ω' ∂(μ.trim hm),
      ∫ η, f η ∂(condExpKernel μ m ω') = ∫ η, f η ∂μ := by
  -- condExp_indep_eq: μ[f|m] =ᵐ[μ] (fun _ ↦ ∫ f ∂μ)
  have h_indep_eq : μ[f|m] =ᵐ[μ] (fun _ : Ω => ∫ y, f y ∂μ) :=
    MeasureTheory.condExp_indep_eq hm' hm hf_meas h_indep
  -- Both sides are m-strongly-measurable, lift to (μ.trim hm)-a.e.
  have h_lhs_meas : StronglyMeasurable[m] (μ[f|m]) :=
    stronglyMeasurable_condExp
  have h_rhs_meas : StronglyMeasurable[m] (fun _ : Ω => ∫ y, f y ∂μ) :=
    stronglyMeasurable_const
  have h_indep_eq_trim : μ[f|m] =ᵐ[μ.trim hm] (fun _ : Ω => ∫ y, f y ∂μ) :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
      h_lhs_meas h_rhs_meas h_indep_eq
  -- condExp_ae_eq_trim_integral_condExpKernel:
  --   μ[f|m] =ᵐ[μ.trim hm] (fun ω' ↦ ∫ f d κ(ω'))
  have h_kernel_eq := condExp_ae_eq_trim_integral_condExpKernel hm hf_int
  -- Combine.
  filter_upwards [h_indep_eq_trim, h_kernel_eq] with ω' h1 h2
  rw [← h2, h1]

/-- **Mathlib upstream candidate (set-version of Helper 2)**: under independence of
`m, m'`, for any `m'`-measurable set `s`, the conditional kernel mass at `s`
equals the unconditional measure of `s`, for `μ.trim hm`-a.e. `ω'`.

**Proof**: apply Helper 2 (`integral_condExpKernel_of_indep`) to the indicator
function `1_s : Ω → ℝ`, which is `m'`-strongly-measurable and bounded (hence
integrable on the finite measure `μ`). The two integrals are
`(κ ω').real s` and `μ.real s` respectively. Since both measures are finite,
the toReal equality lifts back to ENNReal equality.

TODO: Mathlib upstream candidate. -/
@[category API, AMS 11]
lemma condExpKernel_apply_eq_of_indep
    {Ω : Type*} {m m' mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) (hm' : m' ≤ mΩ)
    (h_indep : Indep m' m μ)
    {s : Set Ω} (hs : MeasurableSet[m'] s) :
    ∀ᵐ ω' ∂(μ.trim hm),
      condExpKernel μ m ω' s = μ s := by
  -- Apply Helper 2 to the indicator function of s.
  have hs_top : MeasurableSet s := hm' s hs
  have h_ind_meas : StronglyMeasurable[m'] (s.indicator (fun _ : Ω => (1 : ℝ))) :=
    (stronglyMeasurable_const (b := (1 : ℝ))).indicator hs
  have h_ind_meas_top : Measurable (s.indicator (fun _ : Ω => (1 : ℝ))) :=
    (measurable_const).indicator hs_top
  have h_ind_int : Integrable (s.indicator (fun _ : Ω => (1 : ℝ))) μ := by
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
      h_ind_meas_top.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ s
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have h_helper2 := integral_condExpKernel_of_indep
    (μ := μ) hm hm' h_indep h_ind_meas h_ind_int
  filter_upwards [h_helper2] with ω' hω'
  -- ∫ 1_s dκ(ω') = (κ ω').real s, ∫ 1_s dμ = μ.real s
  have h_int_κ : ∫ y, s.indicator (fun _ : Ω => (1 : ℝ)) y ∂(condExpKernel μ m ω') =
      (condExpKernel μ m ω').real s := by
    rw [integral_indicator hs_top, setIntegral_const, smul_eq_mul, mul_one]
  have h_int_μ : ∫ y, s.indicator (fun _ : Ω => (1 : ℝ)) y ∂μ = μ.real s := by
    rw [integral_indicator hs_top, setIntegral_const, smul_eq_mul, mul_one]
  rw [h_int_κ, h_int_μ] at hω'
  -- Convert from .real equality to ENNReal equality.
  have h_κ_finite : condExpKernel μ m ω' s ≠ ⊤ := measure_ne_top _ _
  have h_μ_finite : μ s ≠ ⊤ := measure_ne_top _ _
  have h_eq := congrArg ENNReal.ofReal hω'
  rwa [show (condExpKernel μ m ω').real s = (condExpKernel μ m ω' s).toReal from rfl,
       show μ.real s = (μ s).toReal from rfl,
       ENNReal.ofReal_toReal h_κ_finite,
       ENNReal.ofReal_toReal h_μ_finite] at h_eq

/-- **Mathlib upstream candidate (Helper 3 — finite-family version)**:
For independent σ-algebras `m, m'` under `μ`, and an `m'`-measurable family
`(X i)_i` over a finite index set that is `iIndepFun` under `μ`, the family
remains `iIndepFun` under the conditional kernel `condExpKernel μ m ω'` in the
*kernel* sense: for any choice of measurable sets in the comap σ-algebras, the
product formula holds for `μ.trim hm`-a.e. `ω'`.

**Proof**: by definition of `Kernel.iIndepFun`, we need to show, for any
`Finset s` and any choice `(f' : ι → Set Ω)` with `f' i ∈ comap (X i)`, that
`∀ᵐ ω' ∂(μ.trim hm), (κ ω')(⋂ i ∈ s, f' i) = ∏ i ∈ s, (κ ω')(f' i)`.

Each `f' i` is an `m'`-measurable set (since `comap (X i) ⊆ m'`). Apply
`condExpKernel_apply_eq_of_indep` to each of `⋂ f' i, f' i_1, ..., f' i_n`,
take finite intersection of the resulting a.e. sets. Inside the intersection,
`κ(ω')` agrees with `μ` on each set, and `μ` satisfies the product formula
by `iIndepFun.meas_biInter`.

TODO: Mathlib upstream candidate. -/
@[category API, AMS 11]
lemma iIndepFun_condExpKernel_of_indep_of_indep
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {Ω : Type*} {m m' mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) (hm' : m' ≤ mΩ)
    (h_indep : Indep m' m μ)
    {X : (i : ι) → Ω → β i}
    (hX_meas : ∀ i, @Measurable _ _ m' _ (X i))
    (hX_iIndep : ProbabilityTheory.iIndepFun X μ) :
    ProbabilityTheory.Kernel.iIndepFun X (condExpKernel μ m) (μ.trim hm) := by
  -- Unfold: need ∀ s f', (∀ i ∈ s, f' i ∈ comap (X i)) →
  --   ∀ᵐ ω' ∂(μ.trim hm), (κ ω')(⋂ f' i) = ∏ (κ ω')(f' i)
  intro s f' h_f'_mem
  -- Each f' i is m'-measurable since comap (X i) ⊆ m'.
  have h_f'_meas_m' : ∀ i ∈ s, MeasurableSet[m'] (f' i) := by
    intro i hi
    have h_f'_in_comap : MeasurableSet[(inferInstance : MeasurableSpace (β i)).comap (X i)]
        (f' i) := h_f'_mem i hi
    obtain ⟨t, _, hts⟩ := h_f'_in_comap
    rw [← hts]
    exact (hX_meas i) ‹_›
  have h_f'_meas_top : ∀ i ∈ s, MeasurableSet (f' i) := fun i hi => hm' _ (h_f'_meas_m' i hi)
  -- Apply condExpKernel_apply_eq_of_indep to each f' i and to ⋂ i ∈ s, f' i.
  have h_per_i : ∀ i ∈ s, ∀ᵐ ω' ∂(μ.trim hm),
      condExpKernel μ m ω' (f' i) = μ (f' i) :=
    fun i hi => condExpKernel_apply_eq_of_indep hm hm' h_indep (h_f'_meas_m' i hi)
  have h_inter_meas_m' : MeasurableSet[m'] (⋂ i ∈ s, f' i) := by
    haveI : MeasurableSpace Ω := m'
    exact MeasurableSet.biInter s.countable_toSet (fun i hi => h_f'_meas_m' i hi)
  have h_inter : ∀ᵐ ω' ∂(μ.trim hm),
      condExpKernel μ m ω' (⋂ i ∈ s, f' i) = μ (⋂ i ∈ s, f' i) :=
    condExpKernel_apply_eq_of_indep hm hm' h_indep h_inter_meas_m'
  -- μ-side product formula via iIndepFun.
  have h_μ_prod : μ (⋂ i ∈ s, f' i) = ∏ i ∈ s, μ (f' i) :=
    hX_iIndep.meas_biInter h_f'_mem
  -- Cleaner: use ae_ball_iff for the per-i intersection.
  have h_per_i_all : ∀ᵐ ω' ∂(μ.trim hm),
      ∀ i (hi : i ∈ (s : Set ι)), condExpKernel μ m ω' (f' i) = μ (f' i) := by
    rw [ae_ball_iff s.countable_toSet]
    intro i hi
    exact h_per_i i hi
  filter_upwards [h_inter, h_per_i_all] with ω' h_inter_ω h_per_i_ω
  rw [h_inter_ω, h_μ_prod]
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact (h_per_i_ω i hi).symm

/-- **Mathlib upstream candidate**: The π-system generated by a countable family of
sets is countable.

**Proof**: define a sequence `T : ℕ → Set (Set α)` with `T 0 := s` and
`T (n+1) := T n ∪ image2 (· ∩ ·) (T n) (T n)`. Each `T n` is countable (by induction
+ `Set.Countable.image2`); the union `⋃ n, T n` is countable. Show
`generatePiSystem s ⊆ ⋃ n, T n` by induction on the `generatePiSystem` structure
(base: `s ⊆ T 0`; inductive step: if `u ∈ T m`, `v ∈ T n`, then
`u ∩ v ∈ T (max m n + 1)`).

TODO: Mathlib upstream candidate. -/
@[category API, AMS 11]
lemma generatePiSystem_countable {α : Type*} {s : Set (Set α)} (h : s.Countable) :
    (generatePiSystem s).Countable := by
  -- Define recursive layer T : ℕ → Set (Set α).
  let T : ℕ → Set (Set α) := fun n => Nat.recAux s
    (fun _ Tn => Tn ∪ Set.image2 (· ∩ ·) Tn Tn) n
  have hT_zero : T 0 = s := rfl
  have hT_succ : ∀ n, T (n + 1) = T n ∪ Set.image2 (· ∩ ·) (T n) (T n) := fun _ => rfl
  -- Each T n is countable.
  have hT_countable : ∀ n, (T n).Countable := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      rw [hT_succ]
      exact ih.union (ih.image2 ih (· ∩ ·))
  -- T is monotone: T n ⊆ T (n+1).
  have hT_mono_succ : ∀ n, T n ⊆ T (n + 1) := by
    intro n; rw [hT_succ]; exact Set.subset_union_left
  have hT_mono : ∀ {m n}, m ≤ n → T m ⊆ T n := by
    intro m n hmn
    induction hmn with
    | refl => exact Set.Subset.rfl
    | step _ ih => exact ih.trans (hT_mono_succ _)
  -- Every element of generatePiSystem s is in some T n.
  have h_subset : generatePiSystem s ⊆ ⋃ n, T n := by
    intro x hx
    induction hx with
    | base h_s => exact Set.mem_iUnion.mpr ⟨0, h_s⟩
    | inter _ _ _ ih_u ih_v =>
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ih_u
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ih_v
      refine Set.mem_iUnion.mpr ⟨max m n + 1, ?_⟩
      rw [hT_succ]
      refine Or.inr ?_
      exact ⟨_, hT_mono (le_max_left m n) hm, _, hT_mono (le_max_right m n) hn, rfl⟩
  -- ⋃ n, T n is countable.
  have h_union_countable : (⋃ n, T n).Countable :=
    Set.countable_iUnion (fun n => hT_countable n)
  exact h_union_countable.mono h_subset

/-- **Mathlib upstream candidate scaffold (Path X — Kernel→Measure iIndepFun extraction)**:
For a `Kernel.iIndepFun` family of measurable functions valued in countably-generated
measurable spaces with finite index, the family is `iIndepFun` under each fiber `κ(ω')`
for `ν`-almost every `ω'`. This intermediate result extracts the **seed-level**
`iIndepSets` for `ν`-a.e. `ω'`, which is the structural core; the full extension
to `iIndepFun X (κ ω')` requires extending iIndepSets from the countable seed to
its π-system closure (Dynkin-system / π-system extension argument), which is a
focused Mathlib upstream candidate (the proof of `Kernel.iIndepSets.iIndep`
already implements this internally for the kernel-level statement; the per-fiber
Measure-level version is symmetric).

**Proof outline**:
1. For each `i`, take a countable generating set `g_i` for `m_β i` (via
   `MeasurableSpace.countableGeneratingSet`).
2. Form the pulled-back set system `s'_i := { (X i)^{-1}(t) | t ∈ g_i }`. Each
   `s'_i` is countable, and `(X i)^{-1} '' g_i` generates `comap (X i) (m_β i)`
   via `comap_generateFrom`.
3. For each fixed `(S : Finset ι, f : ι → Set Ω)` with `f i ∈ s'_i` for `i ∈ S`,
   `Kernel.iIndepFun X κ ν` gives `∀ᵐ ω' ∂ν, κ(ω')(⋂_i f i) = ∏_i κ(ω')(f i)`.
4. The set of such `(S, f)` is COUNTABLE (finite ι, countable s'_i). Take
   countable intersection of a.e. sets ⇒ uniform a.e. set `A`.
5. Inside `A`: get `iIndepSets s' (κ ω')` at the seed level.

The full statement `∀ᵐ ω' ∂ν, iIndepFun X (κ ω')` (the per-fiber Measure-level
`iIndepFun`) requires the π-system extension step (Mathlib upstream candidate).

**Output**: `∀ᵐ ω' ∂ν, iIndepSets s' (κ ω')` — the seed-level form, which is
provable cleanly. -/
@[category API, AMS 11]
theorem Kernel.iIndepFun.iIndepSets_apply_ae_seed
    {ι : Type*} [Fintype ι] {β : ι → Type*} [m_β : ∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSpace.CountablyGenerated (β i)]
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {_mΩ' : MeasurableSpace Ω'}
    {κ : Kernel Ω' Ω} {ν : Measure Ω'}
    {X : ∀ i, Ω → β i} (_hX_meas : ∀ i, Measurable (X i))
    (h : ProbabilityTheory.Kernel.iIndepFun X κ ν) :
    let s' : ι → Set (Set Ω) := fun i =>
      Set.image (fun t : Set (β i) => (X i) ⁻¹' t)
        (MeasurableSpace.countableGeneratingSet (β i))
    ∀ᵐ ω' ∂ν, ProbabilityTheory.iIndepSets s' (κ ω') := by
  classical
  -- Step 1: countable generating sets g_i ⊆ Set (β i) for each m_β i.
  let g : ∀ i, Set (Set (β i)) := fun i => MeasurableSpace.countableGeneratingSet (β i)
  have hg_countable : ∀ i, (g i).Countable :=
    fun i => MeasurableSpace.countable_countableGeneratingSet (α := β i)
  have hg_meas : ∀ i, ∀ s ∈ g i, MeasurableSet s := fun i s hs =>
    MeasurableSpace.measurableSet_countableGeneratingSet hs
  have hg_generate : ∀ i, m_β i = MeasurableSpace.generateFrom (g i) := fun i =>
    (MeasurableSpace.generateFrom_countableGeneratingSet (α := β i)).symm
  -- Step 2: pulled-back set system s'_i := { (X i)^{-1}(t) | t ∈ g i }.
  let s' : ∀ _ : ι, Set (Set Ω) := fun i => Set.image (fun t : Set (β i) => (X i) ⁻¹' t) (g i)
  have hs'_countable : ∀ i, (s' i).Countable := fun i => (hg_countable i).image _
  have hs'_generate : ∀ i, (m_β i).comap (X i) = MeasurableSpace.generateFrom (s' i) := by
    intro i
    rw [hg_generate i, MeasurableSpace.comap_generateFrom]
  -- Step 3: for each (S : Finset ι, f : ι → Set Ω) with f i ∈ s' i for i ∈ S,
  -- Kernel.iIndepFun gives the product formula a.e.
  have h_iIndepSets_kernel : ProbabilityTheory.Kernel.iIndepSets s' κ ν := by
    intro S f hf_mem
    have hf_meas : ∀ i ∈ S, MeasurableSet[(m_β i).comap (X i)] (f i) := by
      intro i hi
      rw [hs'_generate i]
      exact MeasurableSpace.measurableSet_generateFrom (hf_mem i hi)
    exact h S hf_meas
  -- Step 4: take countable intersection over (S, ψ).
  haveI : ∀ i, Countable ↥(s' i) := fun i => (hs'_countable i).to_subtype
  haveI : Countable (Finset ι) := by infer_instance
  have h_joint : ∀ᵐ ω' ∂ν,
      ∀ (S : Finset ι) (ψ : ∀ i, ↥(s' i)),
      κ ω' (⋂ i ∈ S, (ψ i : Set Ω)) = ∏ i ∈ S, κ ω' ((ψ i : Set Ω)) := by
    rw [ae_all_iff]
    intro S
    rw [ae_all_iff]
    intro ψ
    have hf_mem : ∀ i ∈ S, (ψ i : Set Ω) ∈ s' i := fun i _ => (ψ i).property
    exact h_iIndepSets_kernel S hf_mem
  -- Step 5: extract iIndepSets s' (κ ω') from the joint statement.
  filter_upwards [h_joint] with ω' h_ω'
  -- Translate the joint product formula into Measure-level iIndepSets.
  -- Measure-level iIndepSets unfolds to Kernel.iIndepSets with const kernel + dirac measure.
  intro S ψ hψ_mem
  refine MeasureTheory.ae_of_all _ (fun _ => ?_)
  simp only [ProbabilityTheory.Kernel.const_apply]
  -- ψ : ι → Set Ω with ψ i ∈ s' i for i ∈ S. Build ψ' : ∀ i, ↥(s' i).
  have hg_nonempty : ∀ i, (s' i).Nonempty := fun i => by
    have h_g_ne : (g i).Nonempty := MeasurableSpace.nonempty_countableGeneratingSet (α := β i)
    obtain ⟨t, ht⟩ := h_g_ne
    exact ⟨(X i) ⁻¹' t, t, ht, rfl⟩
  let ψ' : ∀ i, ↥(s' i) := fun i =>
    if hi : i ∈ S then ⟨ψ i, hψ_mem i hi⟩
    else ⟨(hg_nonempty i).choose, (hg_nonempty i).choose_spec⟩
  have h_ψ'_eq : ∀ i ∈ S, (ψ' i : Set Ω) = ψ i := by
    intro i hi
    simp [ψ', dif_pos hi]
  have h_inter_eq : (⋂ i ∈ S, ψ i) = (⋂ i ∈ S, (ψ' i : Set Ω)) := by
    refine Set.iInter_congr (fun i => ?_)
    refine Set.iInter_congr_Prop Iff.rfl ?_
    intro hi; rw [h_ψ'_eq i hi]
  have h_prod_eq : (∏ i ∈ S, (κ ω') (ψ i)) = (∏ i ∈ S, (κ ω') ((ψ' i : Set Ω))) :=
    Finset.prod_congr rfl (fun i hi => by rw [h_ψ'_eq i hi])
  rw [h_inter_eq, h_prod_eq]
  exact h_ω' S ψ'

/-- **Mathlib upstream candidate (Path X proper — Kernel→Measure iIndepFun extraction)**:
For a `Kernel.iIndepFun` family of measurable functions valued in countably-generated
measurable spaces with finite index, the family is `iIndepFun` under each fiber `κ(ω')`
for `ν`-almost every `ω'`.

**Proof outline**:
1. For each `i`, take a countable generating set `g_i` for `m_β i`. Form
   `s'_i := { (X i)^{-1}(t) | t ∈ g_i }` — countable, generates the comap σ-algebra.
2. Form the π-system `π i := generatePiSystem (s' i)` — countable (by
   `generatePiSystem_countable`), still generates the comap σ-algebra
   (by `generateFrom_generatePiSystem_eq`), and is a π-system
   (by `isPiSystem_generatePiSystem`).
3. Each element of `π i` is in the comap σ-algebra (by `generatePiSystem_measurableSet`
   applied with the comap σ-algebra). For each fixed `(S, f)` with `f i ∈ π i`,
   `Kernel.iIndepFun X κ ν` gives the product formula a.e.
4. Take countable intersection over `(S, ψ : ∀ i, ↥(π i))` (countable since `Finset ι`
   countable + each `π i` countable) to get a uniform a.e. set: `iIndepSets π (κ ω')`.
5. Apply `iIndepSets.iIndep` (Measure-level) to extend to
   `iIndep (fun i => (m_β i).comap (X i)) (κ ω')`.
6. Conclude `iIndepFun X (κ ω')` via `iIndepFun_iff_iIndep`.

TODO: Mathlib upstream candidate. -/
@[category API, AMS 11]
theorem Kernel.iIndepFun.iIndepFun_apply_ae
    {ι : Type*} [Fintype ι] {β : ι → Type*} [m_β : ∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSpace.CountablyGenerated (β i)]
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {_mΩ' : MeasurableSpace Ω'}
    {κ : Kernel Ω' Ω} {ν : Measure Ω'}
    {X : ∀ i, Ω → β i} (hX_meas : ∀ i, Measurable (X i))
    (h : ProbabilityTheory.Kernel.iIndepFun X κ ν) :
    ∀ᵐ ω' ∂ν, ProbabilityTheory.iIndepFun X (κ ω') := by
  classical
  -- Step 1: countable generating sets g_i ⊆ Set (β i) for each m_β i.
  let g : ∀ i, Set (Set (β i)) := fun i => MeasurableSpace.countableGeneratingSet (β i)
  have hg_countable : ∀ i, (g i).Countable :=
    fun i => MeasurableSpace.countable_countableGeneratingSet (α := β i)
  have hg_meas : ∀ i, ∀ s ∈ g i, MeasurableSet s := fun i s hs =>
    MeasurableSpace.measurableSet_countableGeneratingSet hs
  have hg_generate : ∀ i, m_β i = MeasurableSpace.generateFrom (g i) := fun i =>
    (MeasurableSpace.generateFrom_countableGeneratingSet (α := β i)).symm
  -- Step 2: pulled-back set system s'_i := { (X i)^{-1}(t) | t ∈ g i }.
  let s' : ∀ _ : ι, Set (Set Ω) := fun i => Set.image (fun t : Set (β i) => (X i) ⁻¹' t) (g i)
  have hs'_countable : ∀ i, (s' i).Countable := fun i => (hg_countable i).image _
  have hs'_generate : ∀ i, (m_β i).comap (X i) = MeasurableSpace.generateFrom (s' i) := by
    intro i
    rw [hg_generate i, MeasurableSpace.comap_generateFrom]
  -- Step 2.5: π-system extension. π i := generatePiSystem (s' i).
  let π : ∀ _ : ι, Set (Set Ω) := fun i => generatePiSystem (s' i)
  have hπ_countable : ∀ i, (π i).Countable := fun i => generatePiSystem_countable (hs'_countable i)
  have hπ_isPi : ∀ i, IsPiSystem (π i) := fun i => isPiSystem_generatePiSystem _
  have hπ_generate : ∀ i, (m_β i).comap (X i) = MeasurableSpace.generateFrom (π i) := by
    intro i
    rw [hs'_generate i, generateFrom_generatePiSystem_eq]
  -- Each element of π i is measurable in comap σ-algebra.
  have hπ_meas : ∀ i, ∀ t ∈ π i, MeasurableSet[(m_β i).comap (X i)] t := by
    intro i t ht
    rw [hπ_generate i]
    exact MeasurableSpace.measurableSet_generateFrom ht
  -- Step 3: from Kernel.iIndepFun, derive Kernel.iIndepSets π κ ν.
  have h_iIndepSets_kernel : ProbabilityTheory.Kernel.iIndepSets π κ ν := by
    intro S f hf_mem
    have hf_meas : ∀ i ∈ S, MeasurableSet[(m_β i).comap (X i)] (f i) :=
      fun i hi => hπ_meas i (f i) (hf_mem i hi)
    exact h S hf_meas
  -- Step 4: take countable intersection over (S, ψ : ∀ i, ↥(π i)).
  haveI : ∀ i, Countable ↥(π i) := fun i => (hπ_countable i).to_subtype
  haveI : Countable (Finset ι) := by infer_instance
  have h_joint : ∀ᵐ ω' ∂ν,
      ∀ (S : Finset ι) (ψ : ∀ i, ↥(π i)),
      κ ω' (⋂ i ∈ S, (ψ i : Set Ω)) = ∏ i ∈ S, κ ω' ((ψ i : Set Ω)) := by
    rw [ae_all_iff]
    intro S
    rw [ae_all_iff]
    intro ψ
    have hf_mem : ∀ i ∈ S, (ψ i : Set Ω) ∈ π i := fun i _ => (ψ i).property
    exact h_iIndepSets_kernel S hf_mem
  -- Step 5: from joint product formula, get iIndepSets π (κ ω') for a.e. ω'.
  filter_upwards [h_joint] with ω' h_ω'
  -- Build iIndepSets at the Measure level.
  have h_iIndepSets_measure : ProbabilityTheory.iIndepSets π (κ ω') := by
    intro S ψ hψ_mem
    refine MeasureTheory.ae_of_all _ (fun _ => ?_)
    simp only [ProbabilityTheory.Kernel.const_apply]
    -- Build ψ' : ∀ i, ↥(π i).
    have hπ_nonempty : ∀ i, (π i).Nonempty := fun i => by
      have h_s'_ne : (s' i).Nonempty := by
        have h_g_ne : (g i).Nonempty := MeasurableSpace.nonempty_countableGeneratingSet (α := β i)
        obtain ⟨t, ht⟩ := h_g_ne
        exact ⟨(X i) ⁻¹' t, t, ht, rfl⟩
      obtain ⟨u, hu⟩ := h_s'_ne
      exact ⟨u, generatePiSystem.base hu⟩
    let ψ' : ∀ i, ↥(π i) := fun i =>
      if hi : i ∈ S then ⟨ψ i, hψ_mem i hi⟩
      else ⟨(hπ_nonempty i).choose, (hπ_nonempty i).choose_spec⟩
    have h_ψ'_eq : ∀ i ∈ S, (ψ' i : Set Ω) = ψ i := by
      intro i hi
      simp [ψ', dif_pos hi]
    have h_inter_eq : (⋂ i ∈ S, ψ i) = (⋂ i ∈ S, (ψ' i : Set Ω)) := by
      refine Set.iInter_congr (fun i => ?_)
      refine Set.iInter_congr_Prop Iff.rfl ?_
      intro hi; rw [h_ψ'_eq i hi]
    have h_prod_eq : (∏ i ∈ S, (κ ω') (ψ i)) = (∏ i ∈ S, (κ ω') ((ψ' i : Set Ω))) :=
      Finset.prod_congr rfl (fun i hi => by rw [h_ψ'_eq i hi])
    rw [h_inter_eq, h_prod_eq]
    exact h_ω' S ψ'
  -- Step 6: extend iIndepSets π → iIndep (comap (X i)) using iIndepSets.iIndep.
  have h_le' : ∀ i, (m_β i).comap (X i) ≤ mΩ := fun i => (hX_meas i).comap_le
  have h_iIndep : ProbabilityTheory.iIndep (fun i => (m_β i).comap (X i)) (κ ω') :=
    ProbabilityTheory.iIndepSets.iIndep (m := fun i => (m_β i).comap (X i))
      h_le' π hπ_isPi hπ_generate h_iIndepSets_measure
  -- Step 7: conclude iIndepFun X (κ ω').
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  exact h_iIndep

end CondExpKernelHelpers

/-- **Per-`w` integrability helper**: `|Re(c_w · (Y_w - α))| ≤ 2` deterministically,
hence `exp(t · Re(c_w · (Y_w - α)))` is integrable on the probability measure
`apssvEtaMeasure` for every `t`. Direct from `apssvBlockSum_centered_summand_norm_le_two`
+ `Complex.abs_re_le_norm` + boundedness on a probability measure. -/
@[category API, AMS 11]
lemma apssv_per_w_summand_re_integrable_exp (P k : ℕ) {r : ℕ} (w : Fin r → Bool) (t : ℝ) :
    MeasureTheory.Integrable
      (fun η : List Bool → Bool => Real.exp (t *
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re))
      apssvEtaMeasure := by
  -- Measurability of the integrand.
  have h_meas_J : Measurable (fun η : List Bool → Bool => apssvJ η r w) := apssvJ_measurable r w
  have h_meas_T : Measurable (fun η : List Bool → Bool => apssvT η w P) := apssvT_measurable w P
  have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
  have h_J_real : Measurable (fun η : List Bool → Bool => (apssvJ η r w : ℝ)) :=
    h_natCast_real.comp h_meas_J
  have h_e_cont : Continuous (fun t : ℝ => e ((k : ℝ) * t / (2 : ℝ) ^ r)) := by
    unfold e
    exact Complex.continuous_exp.comp (by continuity)
  have h_c_meas : Measurable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
    h_e_cont.measurable.comp h_J_real
  have h_Y_meas : Measurable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
    h_e_cont.measurable.comp h_meas_T
  have h_centered_meas : Measurable
      (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)) :=
    h_c_meas.mul (h_Y_meas.sub measurable_const)
  have h_re_meas : Measurable
      (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) :=
    Complex.measurable_re.comp h_centered_meas
  have h_meas : Measurable
      (fun η : List Bool → Bool => Real.exp (t *
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)) :=
    Real.measurable_exp.comp (h_re_meas.const_mul t)
  -- Bound: |Re(centered summand)| ≤ 2 deterministically (Complex.abs_re_le_norm + ‖·‖ ≤ 2).
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const
      (Real.exp (|t| * 2)))
    h_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
  intro η
  have h_norm_le : ‖e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
      (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
        ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)‖ ≤ 2 :=
    apssvBlockSum_centered_summand_norm_le_two η P k w w
  have h_re_abs : |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
      (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
        ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re| ≤ 2 :=
    (Complex.abs_re_le_norm _).trans h_norm_le
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have h_t_re_le : t * (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
      (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
        ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re ≤
      |t| * 2 := by
    have h1 : t * (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re ≤
        |t * (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re| :=
      le_abs_self _
    rw [abs_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h_re_abs (abs_nonneg _)
  exact h_t_re_le

/-- **Per-`w` conditional sub-Gaussian MGF** [Phase A]: each centered summand
`Re(c_w · (Y_w - α))` is conditionally sub-Gaussian wrt `apssvShortSigma r` with
parameter `1`.

**Proof structure**:
- `integrable_exp_mul`: closed via `apssv_per_w_summand_re_integrable_exp` (the
  centered summand is bounded by `2`, so `exp(t · X)` is bounded by `exp(2|t|)`,
  integrable on a probability measure). After `condExpKernel_comp_trim` the
  composed-measure integrability reduces to `μ`-integrability.
- `mgf_le` [REMAINING]: for `(μ.trim hm)`-a.e. `ω'`, the conditional MGF satisfies
  `mgf X (condExpKernel μ m ω') t ≤ exp(t²/2)`.
  Under `condExpKernel μ apssvShortSigma ω'`:
  * `c_w(η)` is a.s. constant `z_w := c_w(ω')` (m-measurability + condExpKernel
    structure)
  * `Y_w(η)` retains its unconditional law (σ-long ⟂ σ-short via
    `apssv_short_long_indep`, and Y_w is σ-long-measurable)
  * Reduce conditional mgf to `mgf(Re(z_w · (Y_w - α))) μ t`
  * Apply Hoeffding (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) — range 2,
    mean 0 (since `E[Y_w] = α`) — to get bound `exp(t²/2)`. -/
@[category API, AMS 11]
lemma apssv_per_w_HasCondSubgaussianMGF (P k : ℕ) {r : ℕ} (w : Fin r → Bool) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      1 apssvEtaMeasure := by
  -- Unfold to Kernel.HasSubgaussianMGF and construct the structure.
  refine ⟨fun t => ?_, ?_⟩
  · -- integrable_exp_mul: ∀ t, Integrable (exp(t · X)) (condExpKernel μ m ∘ₘ μ.trim hm)
    -- By condExpKernel_comp_trim, this equals Integrable (exp(t · X)) μ.
    rw [ProbabilityTheory.condExpKernel_comp_trim]
    exact apssv_per_w_summand_re_integrable_exp P k w t
  · -- mgf_le: ∀ᵐ ω' ∂(μ.trim hm), ∀ t, mgf X (condExpKernel μ m ω') t ≤ exp(t²/2)
    -- Strategy: use the three helpers above.
    -- 1. Apply Helper 1 to Re(c_w) and Im(c_w) (both σ_short-meas, bounded ≤ 1) to get
    --    c_w =ᵐ[κ(ω')] (const c_w(ω')) for a.e. ω'.
    -- 2. Hence X_w =ᵐ[κ(ω')] (fun η ↦ Re(c_w(ω') · (Y_w(η) - α))) for a.e. ω'.
    -- 3. mgf X_w (κ ω') t = ∫ exp(t · Re(c_w(ω') · (Y_w(η) - α))) dκ(ω').
    -- 4. The integrand is σ_long-measurable (c_w(ω') is a constant in η). By Helper 2,
    --    this integral equals ∫ ... dμ.
    -- 5. By Hoeffding (range 2, mean 0), ∫ ... dμ ≤ exp(t²/2).
    --
    -- Step 4 has a technical wrinkle: Helper 2 is `∀ᵐ ω' ∂μ.trim, integral_eq`, but the
    -- integrand depends on ω' through c_w(ω'). Closed by applying Helper 2 pointwise after
    -- conditioning on the a.e.-determined parameter c_w(ω').
    -- Abbreviations: μ, m, m', α, c_w, Y_w (kept as plain definitions to avoid
    -- typeclass-instance shadowing issues).
    have hm_le : apssvShortSigma r ≤ MeasurableSpace.pi := apssvShortSigma_le r
    have hm'_le : apssvLongSigma r ≤ MeasurableSpace.pi := apssvLongSigma_le r
    -- α := ∫ Y_w dμ
    set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure with hα_def
    -- Norm bounds
    have h_norm_α : ‖α‖ ≤ 1 := apssvT_e_integral_norm_le_one w P k r
    -- σ-measurability of c_w under apssvShortSigma r and Y_w under apssvLongSigma r
    have h_c_meas_short : @Measurable _ _ (apssvShortSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      apssvBlockSum_c_apssvShortSigma_measurable r w k
    have h_Y_meas_long : @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      apssvBlockSum_Y_apssvLongSigma_measurable w P k
    have h_c_meas_top : Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      h_c_meas_short.mono hm_le le_rfl
    have h_Y_meas_top : Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      h_Y_meas_long.mono hm'_le le_rfl
    -- Re/Im of c_w are apssvShortSigma-strongly-measurable, bounded by 1.
    have h_c_re_meas_short : @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re) := by
      have h := (Complex.measurable_re.comp h_c_meas_short :
        @Measurable _ _ (apssvShortSigma r) _ _)
      exact h.stronglyMeasurable
    have h_c_im_meas_short : @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im) := by
      have h := (Complex.measurable_im.comp h_c_meas_short :
        @Measurable _ _ (apssvShortSigma r) _ _)
      exact h.stronglyMeasurable
    have h_c_re_bd : ∀ η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re| ≤ 1 :=
      fun η => (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_c_im_bd : ∀ η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im| ≤ 1 :=
      fun η => (Complex.abs_im_le_norm _).trans (norm_e _).le
    -- Apply Helper 1 twice.
    have h_re_eq := condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
      (μ := apssvEtaMeasure) hm_le h_c_re_meas_short h_c_re_bd
    have h_im_eq := condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
      (μ := apssvEtaMeasure) hm_le h_c_im_meas_short h_c_im_bd
    -- Combine into c_w =ᵐ[κ(ω')] const c_w(ω') for a.e. ω'.
    have h_c_eq_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool => e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)) := by
      filter_upwards [h_re_eq, h_im_eq] with ω' h_re_eq_ω h_im_eq_ω
      filter_upwards [h_re_eq_ω, h_im_eq_ω] with η h_re_η h_im_η
      exact Complex.ext h_re_η h_im_η
    -- Re(Y_w), Im(Y_w) are apssvLongSigma-strongly-measurable, bounded by 1, integrable
    -- under apssvEtaMeasure. Used to apply Helper 2 (`integral_condExpKernel_of_indep`)
    -- to derive mean-zero of Re(Y_w - α), Im(Y_w - α) under κ(ω').
    have h_Y_re_meas_long_strong : @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) := by
      have h := (Complex.measurable_re.comp h_Y_meas_long :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_im_meas_long_strong : @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) := by
      have h := (Complex.measurable_im.comp h_Y_meas_long :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_re_meas_top : Measurable (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) :=
      Complex.measurable_re.comp h_Y_meas_top
    have h_Y_im_meas_top : Measurable (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) :=
      Complex.measurable_im.comp h_Y_meas_top
    have h_Y_re_int : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        apssvEtaMeasure := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_re_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        apssvEtaMeasure := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_im_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    -- Apply Helper 2 to Re(Y_w) and Im(Y_w): a.e. ω', their integral over κ(ω') = unconditional.
    -- This avoids the parametric κ(ω') → μ substitution (the integrand would depend on ω' through z).
    have h_indep_long_short : ProbabilityTheory.Indep
        (apssvLongSigma r) (apssvShortSigma r) apssvEtaMeasure :=
      (apssv_short_long_indep r).symm
    have h_int_Y_re_kernel := integral_condExpKernel_of_indep
      (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
      h_Y_re_meas_long_strong h_Y_re_int
    have h_int_Y_im_kernel := integral_condExpKernel_of_indep
      (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
      h_Y_im_meas_long_strong h_Y_im_int
    filter_upwards [h_c_eq_kernel, h_int_Y_re_kernel, h_int_Y_im_kernel] with
      ω' h_c_eq h_re_int_kernel_eq h_im_int_kernel_eq
    intro t
    set z : ℂ := e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r) with hz_def
    have h_z_norm : ‖z‖ = 1 := norm_e _
    -- Replace c_w(η) by z in the integrand.
    have h_X_eq :
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) =ᵐ[ProbabilityTheory.condExpKernel
              apssvEtaMeasure (apssvShortSigma r) ω']
        (fun η : List Bool → Bool =>
          (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
      filter_upwards [h_c_eq] with η h_c_η
      simp only [h_c_η, hz_def]
    have h_exp_eq :
        (fun η : List Bool → Bool =>
          Real.exp (t * (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re))
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
        (fun η : List Bool → Bool =>
          Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)) := by
      filter_upwards [h_X_eq] with η h_η; rw [h_η]
    -- mgf_X (κ ω') t = ∫ exp(t · Re(z · (Y_w η - α))) dκ(ω').
    have h_mgf_rewrite :
        ProbabilityTheory.mgf
          (fun η : List Bool → Bool =>
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      unfold ProbabilityTheory.mgf
      exact MeasureTheory.integral_congr_ae h_exp_eq
    -- The goal needs unfolding of α (since we use `set` above)
    show ProbabilityTheory.mgf _ _ t ≤ Real.exp (((1 : NNReal) : ℝ) * t ^ 2 / 2)
    rw [h_mgf_rewrite]
    -- σ_long-measurability of (fun η ↦ exp(t · Re(z · (Y_w η - α)))).
    have h_inner_meas_long : @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool =>
          Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)) := by
      have h1 : @Measurable _ _ (apssvLongSigma r) _
          (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) :=
        h_Y_meas_long.sub_const α
      have h2 : @Measurable _ _ (apssvLongSigma r) _
          (fun η : List Bool → Bool => z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)) :=
        h1.const_mul z
      have h3 : @Measurable _ _ (apssvLongSigma r) _
          (fun η : List Bool → Bool =>
            (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) :=
        Complex.measurable_re.comp h2
      exact Real.measurable_exp.comp (h3.const_mul t)
    have h_inner_meas_top : Measurable (fun η : List Bool → Bool =>
        Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)) :=
      h_inner_meas_long.mono hm'_le le_rfl
    -- Bound on Re(z · (Y - α)) ∈ [a, b] with b - a = 2.
    have h_norm_Y : ∀ η : List Bool → Bool,
        ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)‖ = 1 := fun η => norm_e _
    set a : ℝ := -1 - (z * α).re with ha_def
    set b : ℝ := 1 - (z * α).re with hb_def
    have h_b_sub_a : b - a = 2 := by show (1 - (z * α).re) - (-1 - (z * α).re) = 2; ring
    have h_re_in_Icc : ∀ η : List Bool → Bool,
        (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re ∈ Set.Icc a b := by
      intro η
      have h_zY : |(z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re| ≤ 1 :=
        (Complex.abs_re_le_norm _).trans
          (by rw [norm_mul, h_z_norm, h_norm_Y]; norm_num)
      constructor
      · -- (z · (Y - α)).re = (z · Y).re - (z · α).re ≥ a = -1 - (z·α).re
        have h_eq : (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
            (z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - (z * α).re := by
          rw [show z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
              z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - z * α from by ring,
              Complex.sub_re]
        rw [h_eq, ha_def]
        linarith [neg_le_of_abs_le h_zY]
      · have h_eq : (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
            (z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - (z * α).re := by
          rw [show z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
              z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - z * α from by ring,
              Complex.sub_re]
        rw [h_eq, hb_def]
        linarith [le_of_abs_le h_zY]
    -- Step 4 (refactored): Apply Hoeffding directly under κ(ω') instead of
    -- substituting to μ. This sidesteps the parametric Helper 2 issue (the
    -- substitution `∫ exp(t · Re(z · (Y_w - α))) d κ(ω') = ∫ ... dμ` would
    -- require Helper 2 with an integrand depending on ω' through z = c_w(ω');
    -- Helper 2 is fixed-integrand, so we'd need a parametric variant). Instead:
    -- compute mean 0 under κ(ω') from `h_re_int_kernel_eq`, `h_im_int_kernel_eq`
    -- (Helper 2 applied to Re(Y_w), Im(Y_w) — fixed integrands, no z parameter),
    -- then apply Hoeffding to κ(ω').
    -- κ(ω') is a probability measure (condExpKernel is Markov).
    haveI h_κ_prob : MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r)) ω'
    -- Compute ∫ Re(Y_w - α) d κ(ω') = 0 and ∫ Im(Y_w - α) d κ(ω') = 0 (a.e. ω').
    -- Uses h_re_int_kernel_eq, h_im_int_kernel_eq from outer filter_upwards.
    have h_int_Y_unconditional : ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)
        ∂apssvEtaMeasure = α := rfl
    -- ∫ Re(Y_w) dμ = Re(α), ∫ Im(Y_w) dμ = Im(α).
    have h_Y_int_unconditional : MeasureTheory.Integrable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := apssvT_e_integrable w P k r
    have h_int_Y_re_unconditional :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure = α.re := by
      show ∫ η, RCLike.re (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.re
      rw [integral_re h_Y_int_unconditional, h_int_Y_unconditional]; rfl
    have h_int_Y_im_unconditional :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure = α.im := by
      show ∫ η, RCLike.im (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.im
      rw [integral_im h_Y_int_unconditional, h_int_Y_unconditional]; rfl
    -- Now under κ(ω'): ∫ Re(Y_w) = α.re, ∫ Im(Y_w) = α.im.
    rw [h_int_Y_re_unconditional] at h_re_int_kernel_eq
    rw [h_int_Y_im_unconditional] at h_im_int_kernel_eq
    -- Mean of Re(z · (Y_w - α)) under κ(ω') = 0:
    -- ∫ Re(z · (Y_w - α)) d κ(ω')
    --   = Re(z) · ∫ Re(Y_w - α) d κ(ω') - Im(z) · ∫ Im(Y_w - α) d κ(ω')
    --   = Re(z) · (α.re - α.re) - Im(z) · (α.im - α.im) = 0.
    have h_Y_re_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_re_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_im_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_int_Y_re_centered_kernel :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      rw [MeasureTheory.integral_sub h_Y_re_int_kernel (MeasureTheory.integrable_const _)]
      rw [h_re_int_kernel_eq, MeasureTheory.integral_const,
          MeasureTheory.probReal_univ, one_smul, sub_self]
    have h_int_Y_im_centered_kernel :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      rw [MeasureTheory.integral_sub h_Y_im_int_kernel (MeasureTheory.integrable_const _)]
      rw [h_im_int_kernel_eq, MeasureTheory.integral_const,
          MeasureTheory.probReal_univ, one_smul, sub_self]
    -- Re(z · (Y - α)) = Re(z)·Re(Y - α) - Im(z)·Im(Y - α). Each part has mean 0 under κ(ω').
    have h_re_meas_top : Measurable
        (fun η : List Bool → Bool =>
          (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
      have h1 : Measurable
          (fun η : List Bool → Bool => z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)) :=
        (h_Y_meas_top.sub_const α).const_mul z
      exact Complex.measurable_re.comp h1
    have h_re_decomp : ∀ η : List Bool → Bool,
        (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
          z.re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
          z.im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) := by
      intro η
      rw [show z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
          (z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - z * α) from by ring]
      rw [Complex.sub_re, Complex.mul_re, Complex.mul_re]; ring
    have h_re_diff_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      h_Y_re_int_kernel.sub (MeasureTheory.integrable_const _)
    have h_im_diff_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      h_Y_im_int_kernel.sub (MeasureTheory.integrable_const _)
    have h_mean_zero_kernel :
        ∫ η, (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      rw [show (fun η : List Bool → Bool =>
            (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) =
          (fun η : List Bool → Bool =>
            z.re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
            z.im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)) from
        funext h_re_decomp]
      rw [MeasureTheory.integral_sub
          (h_re_diff_int_kernel.const_mul z.re) (h_im_diff_int_kernel.const_mul z.im)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [h_int_Y_re_centered_kernel, h_int_Y_im_centered_kernel, mul_zero, mul_zero, sub_zero]
    -- Apply Hoeffding under κ(ω').
    have h_subg_kernel : ProbabilityTheory.HasSubgaussianMGF
        (fun η : List Bool → Bool =>
          (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        ((‖b - a‖₊ / 2) ^ 2)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        h_re_meas_top.aemeasurable
        (Filter.Eventually.of_forall h_re_in_Icc) h_mean_zero_kernel
    have h_param_eq_nn : ((‖b - a‖₊ / 2) ^ 2) = (1 : NNReal) := by
      ext
      push_cast
      rw [show b - a = 2 from h_b_sub_a]
      norm_num
    have h_mgf_le := h_subg_kernel.mgf_le t
    have h_mgf_def :
        ProbabilityTheory.mgf
          (fun η : List Bool → Bool =>
            (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := rfl
    rw [← h_mgf_def]
    refine h_mgf_le.trans ?_
    rw [h_param_eq_nn]

/-- **Per-`w` parametric conditional sub-Gaussian MGF** [Phase D-refactor]:
generalisation of `apssv_per_w_HasCondSubgaussianMGF` over a half-width `H`.

For any half-width `H : NNReal` such that for every unit-modulus `z : ℂ` we can
place `Re(z · (Y_w(η) - α))` inside a real interval of width `2 H` (with center
depending on `z`), the centered summand `Re(c_w · (Y_w - α))` is conditionally
sub-Gaussian wrt `apssvShortSigma r` with parameter `H²`.

**Specialisations**:
- M = 2 case: `H = 1`, center `c_z = -(z · α).re` (using `‖z · Y_w‖ = 1`,
  hence `|Re(z · Y_w)| ≤ 1`, hence `Re(z · (Y_w - α)) ∈ [-1 - (z · α).re,
  1 - (z · α).re]`). See `apssv_per_w_HasCondSubgaussianMGF` (M=2 chassis).
- Linear case: `H = 4π·k/2^r`, center `c_z = 0` (using
  `apssvBlockSum_centered_summand_norm_bound`, `‖z · (Y_w - α)‖ ≤ 4π·k/2^r`,
  hence `|Re(z · (Y_w - α))| ≤ 4π·k/2^r`). See
  `apssv_per_w_HasCondSubgaussianMGF_linear`.

**Proof structure**: identical to M=2 chassis (Helper 1 + Helper 2 → Hoeffding
under κ(ω')); the only z-dependent parts are the range hypothesis + the
Hoeffding parameter `((b-a)/2)² = H²`. -/
@[category API, AMS 11]
lemma apssv_per_w_HasCondSubgaussianMGF_param (P k : ℕ) {r : ℕ} (w : Fin r → Bool)
    (H : NNReal)
    (h_range : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, ∀ η : List Bool → Bool,
      (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re ∈
        Set.Icc (c - (H : ℝ)) (c + (H : ℝ))) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      (H ^ 2) apssvEtaMeasure := by
  refine ⟨fun t => ?_, ?_⟩
  · rw [ProbabilityTheory.condExpKernel_comp_trim]
    exact apssv_per_w_summand_re_integrable_exp P k w t
  · -- mgf_le: same chassis as M=2 case, but with parametric range bound.
    have hm_le : apssvShortSigma r ≤ MeasurableSpace.pi := apssvShortSigma_le r
    have hm'_le : apssvLongSigma r ≤ MeasurableSpace.pi := apssvLongSigma_le r
    set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure with hα_def
    have h_c_meas_short : @Measurable _ _ (apssvShortSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      apssvBlockSum_c_apssvShortSigma_measurable r w k
    have h_Y_meas_long : @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      apssvBlockSum_Y_apssvLongSigma_measurable w P k
    have h_Y_meas_top : Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      h_Y_meas_long.mono hm'_le le_rfl
    have h_c_re_meas_short : @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re) := by
      have h := (Complex.measurable_re.comp h_c_meas_short :
        @Measurable _ _ (apssvShortSigma r) _ _)
      exact h.stronglyMeasurable
    have h_c_im_meas_short : @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im) := by
      have h := (Complex.measurable_im.comp h_c_meas_short :
        @Measurable _ _ (apssvShortSigma r) _ _)
      exact h.stronglyMeasurable
    have h_c_re_bd : ∀ η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re| ≤ 1 :=
      fun η => (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_c_im_bd : ∀ η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im| ≤ 1 :=
      fun η => (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_re_eq := condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
      (μ := apssvEtaMeasure) hm_le h_c_re_meas_short h_c_re_bd
    have h_im_eq := condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
      (μ := apssvEtaMeasure) hm_le h_c_im_meas_short h_c_im_bd
    have h_c_eq_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool => e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)) := by
      filter_upwards [h_re_eq, h_im_eq] with ω' h_re_eq_ω h_im_eq_ω
      filter_upwards [h_re_eq_ω, h_im_eq_ω] with η h_re_η h_im_η
      exact Complex.ext h_re_η h_im_η
    have h_Y_re_meas_long_strong : @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) := by
      have h := (Complex.measurable_re.comp h_Y_meas_long :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_im_meas_long_strong : @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) := by
      have h := (Complex.measurable_im.comp h_Y_meas_long :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_re_meas_top : Measurable (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) :=
      Complex.measurable_re.comp h_Y_meas_top
    have h_Y_im_meas_top : Measurable (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) :=
      Complex.measurable_im.comp h_Y_meas_top
    have h_Y_re_int : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        apssvEtaMeasure := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_re_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        apssvEtaMeasure := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_im_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_indep_long_short : ProbabilityTheory.Indep
        (apssvLongSigma r) (apssvShortSigma r) apssvEtaMeasure :=
      (apssv_short_long_indep r).symm
    have h_int_Y_re_kernel := integral_condExpKernel_of_indep
      (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
      h_Y_re_meas_long_strong h_Y_re_int
    have h_int_Y_im_kernel := integral_condExpKernel_of_indep
      (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
      h_Y_im_meas_long_strong h_Y_im_int
    filter_upwards [h_c_eq_kernel, h_int_Y_re_kernel, h_int_Y_im_kernel] with
      ω' h_c_eq h_re_int_kernel_eq h_im_int_kernel_eq
    intro t
    set z : ℂ := e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r) with hz_def
    have h_z_norm : ‖z‖ = 1 := norm_e _
    have h_X_eq :
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) =ᵐ[ProbabilityTheory.condExpKernel
              apssvEtaMeasure (apssvShortSigma r) ω']
        (fun η : List Bool → Bool =>
          (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
      filter_upwards [h_c_eq] with η h_c_η
      simp only [h_c_η, hz_def]
    have h_exp_eq :
        (fun η : List Bool → Bool =>
          Real.exp (t * (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re))
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
        (fun η : List Bool → Bool =>
          Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)) := by
      filter_upwards [h_X_eq] with η h_η; rw [h_η]
    have h_mgf_rewrite :
        ProbabilityTheory.mgf
          (fun η : List Bool → Bool =>
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      unfold ProbabilityTheory.mgf
      exact MeasureTheory.integral_congr_ae h_exp_eq
    show ProbabilityTheory.mgf _ _ t ≤ Real.exp (((H ^ 2 : NNReal) : ℝ) * t ^ 2 / 2)
    rw [h_mgf_rewrite]
    -- Range bound from parameter h_range.
    obtain ⟨c, h_re_in_Icc⟩ := h_range z h_z_norm
    set a : ℝ := c - (H : ℝ) with ha_def
    set b : ℝ := c + (H : ℝ) with hb_def
    have h_b_sub_a : b - a = 2 * (H : ℝ) := by show (c + (H : ℝ)) - (c - (H : ℝ)) = _; ring
    haveI h_κ_prob : MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r)) ω'
    have h_int_Y_unconditional : ∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)
        ∂apssvEtaMeasure = α := rfl
    have h_Y_int_unconditional : MeasureTheory.Integrable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := apssvT_e_integrable w P k r
    have h_int_Y_re_unconditional :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure = α.re := by
      show ∫ η, RCLike.re (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.re
      rw [integral_re h_Y_int_unconditional, h_int_Y_unconditional]; rfl
    have h_int_Y_im_unconditional :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure = α.im := by
      show ∫ η, RCLike.im (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.im
      rw [integral_im h_Y_int_unconditional, h_int_Y_unconditional]; rfl
    rw [h_int_Y_re_unconditional] at h_re_int_kernel_eq
    rw [h_int_Y_im_unconditional] at h_im_int_kernel_eq
    have h_Y_re_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_re_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        h_Y_im_meas_top.aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_int_Y_re_centered_kernel :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      rw [MeasureTheory.integral_sub h_Y_re_int_kernel (MeasureTheory.integrable_const _)]
      rw [h_re_int_kernel_eq, MeasureTheory.integral_const,
          MeasureTheory.probReal_univ, one_smul, sub_self]
    have h_int_Y_im_centered_kernel :
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      rw [MeasureTheory.integral_sub h_Y_im_int_kernel (MeasureTheory.integrable_const _)]
      rw [h_im_int_kernel_eq, MeasureTheory.integral_const,
          MeasureTheory.probReal_univ, one_smul, sub_self]
    have h_re_meas_top : Measurable
        (fun η : List Bool → Bool =>
          (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
      have h1 : Measurable
          (fun η : List Bool → Bool => z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)) :=
        (h_Y_meas_top.sub_const α).const_mul z
      exact Complex.measurable_re.comp h1
    have h_re_decomp : ∀ η : List Bool → Bool,
        (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
          z.re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
          z.im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) := by
      intro η
      rw [show z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
          (z * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - z * α) from by ring]
      rw [Complex.sub_re, Complex.mul_re, Complex.mul_re]; ring
    have h_re_diff_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      h_Y_re_int_kernel.sub (MeasureTheory.integrable_const _)
    have h_im_diff_int_kernel : MeasureTheory.Integrable
        (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      h_Y_im_int_kernel.sub (MeasureTheory.integrable_const _)
    have h_mean_zero_kernel :
        ∫ η, (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      rw [show (fun η : List Bool → Bool =>
            (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) =
          (fun η : List Bool → Bool =>
            z.re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
            z.im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)) from
        funext h_re_decomp]
      rw [MeasureTheory.integral_sub
          (h_re_diff_int_kernel.const_mul z.re) (h_im_diff_int_kernel.const_mul z.im)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [h_int_Y_re_centered_kernel, h_int_Y_im_centered_kernel, mul_zero, mul_zero, sub_zero]
    have h_re_in_Icc' : ∀ η : List Bool → Bool,
        (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re ∈ Set.Icc a b := by
      intro η; rw [ha_def, hb_def]; exact h_re_in_Icc η
    have h_subg_kernel : ProbabilityTheory.HasSubgaussianMGF
        (fun η : List Bool → Bool =>
          (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        ((‖b - a‖₊ / 2) ^ 2)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        h_re_meas_top.aemeasurable
        (Filter.Eventually.of_forall h_re_in_Icc') h_mean_zero_kernel
    have h_param_eq_nn : ((‖b - a‖₊ / 2) ^ 2) = H ^ 2 := by
      ext
      push_cast
      rw [show b - a = 2 * (H : ℝ) from h_b_sub_a]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (H : ℝ))]
      ring
    have h_mgf_le := h_subg_kernel.mgf_le t
    have h_mgf_def :
        ProbabilityTheory.mgf
          (fun η : List Bool → Bool =>
            (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * (z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := rfl
    rw [← h_mgf_def]
    refine h_mgf_le.trans ?_
    rw [h_param_eq_nn]

/-- **Per-`w` conditional sub-Gaussian MGF (linear bound)** [Phase D]: each
centered summand `Re(c_w · (Y_w - α))` is conditionally sub-Gaussian wrt
`apssvShortSigma r` with parameter `(4π·k/2^r)² = 16π²k²/4^r`.

Specialisation of `apssv_per_w_HasCondSubgaussianMGF_param` at
`H = 4π·k/2^r`, center `c_z = 0` (using
`apssvBlockSum_centered_summand_norm_bound`, `‖z · (Y_w - α)‖ ≤ 4π·k/2^r`).
Sum over `2^r` summands gives the linear sub-Gaussian parameter `16π²k²/2^r`. -/
@[category API, AMS 11]
lemma apssv_per_w_HasCondSubgaussianMGF_linear (P k : ℕ) {r : ℕ} (w : Fin r → Bool) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      (Real.toNNReal (4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r) ^ 2) apssvEtaMeasure := by
  refine apssv_per_w_HasCondSubgaussianMGF_param P k w
    (Real.toNNReal (4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r)) ?_
  intro z hz_norm
  refine ⟨0, fun η => ?_⟩
  set α : ℂ := ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure
  have h_H_nn : (0 : ℝ) ≤ 4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by positivity
  have h_H_coe : (Real.toNNReal (4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r) : ℝ) =
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r :=
    Real.coe_toNNReal _ h_H_nn
  -- Use existing norm bound: ‖e(k·J_η/2^r) · (Y - α)‖ ≤ 4π·k/2^r.
  -- ‖e(k·J_η/2^r)‖ = 1, so ‖Y - α‖ ≤ 4π·k/2^r, hence ‖z · (Y - α)‖ ≤ 4π·k/2^r.
  have h_existing : ‖e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
      (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)‖ ≤
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r :=
    apssvBlockSum_centered_summand_norm_bound η P k w w
  rw [norm_mul, norm_e, one_mul] at h_existing
  have h_norm_z_Y_α : ‖z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)‖ ≤
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r := by
    rw [norm_mul, hz_norm, one_mul]; exact h_existing
  have h_abs_re : |(z * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re| ≤
      4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r :=
    (Complex.abs_re_le_norm _).trans h_norm_z_Y_α
  refine ⟨?_, ?_⟩
  · show 0 - _ ≤ _; rw [h_H_coe]; linarith [neg_le_of_abs_le h_abs_re]
  · show _ ≤ 0 + _; rw [h_H_coe]; linarith [le_of_abs_le h_abs_re]

/-
**Phase B aggregator strategy**: parametrized over a projection
`proj : ℂ → ℝ` (taking the role of `Complex.re` or `Complex.im`). Below, instead
of a generic helper, we write two parallel proofs (Re and Im versions). The key
trick that *almost* bypasses full Helper 3 ("iIndepFun preservation under
condExpKernel"):

After applying Helper 1 to fix `c_w =ᵐ[κ(ω')] z_w := c_w(ω')` for each `w`, the
integrand `exp(t · ∑_w Re(c_w · (Y_w - α)))` becomes
`exp(t · ∑_w Re(z_w · (Y_w - α)))` a.e. on `κ(ω')`. The latter is
`apssvLongSigma r`-measurable (with `z_w` constants), so Helper 2 *would* give the
substitution `∫ ... dκ(ω') = ∫ ... dμ` — IF Helper 2 could be applied with an
ω'-parameterized integrand. Unfortunately Helper 2 takes a fixed integrand and
gives ∀ᵐ ω' ∂μ.trim, so the application requires either (i) a parametric Helper 2
or (ii) the full Helper 3 (iIndepFun preservation under condExpKernel), which
needs π-system + countable-generation arguments.

The proof body below gathers all per-w μ-level facts (per-w sub-Gaussian under μ,
per-w mean zero, per-w iIndepFun) cleanly, but stops at the
substitution-from-κ(ω')-to-μ step, which is the genuine blocker. Under μ we have
sum sub-Gaussian with parameter 2^r via `HasSubgaussianMGF.sum_of_iIndepFun`;
lifting to κ(ω') requires the parametric Helper 2 / Helper 3.
-/

/-- **Phase B aggregator (Re part)**: the centered sum
`∑_w Re(c_w · (Y_w - α))` is conditionally sub-Gaussian wrt `apssvShortSigma r`
with parameter `2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum (P r k : ℕ) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      ((2 : NNReal) ^ r) apssvEtaMeasure := by
  refine ⟨fun t => ?_, ?_⟩
  · -- integrability: each per-w summand is integrable, sum of integrables is integrable.
    -- However we have exp(t · ∑) not ∑ exp(t · ·). We use the bound
    -- |∑_w Re(c_w·(Y_w-α))| ≤ ∑_w 2 = 2 · 2^r, hence exp(t · ·) ≤ exp(|t| · 2^(r+1)).
    rw [ProbabilityTheory.condExpKernel_comp_trim]
    -- Show: Integrable (fun η ↦ exp (t * ∑_w X_w η)) μ.
    have h_meas_T : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvT η w P) :=
      fun w => apssvT_measurable w P
    have h_meas_J : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvJ η r w) :=
      fun w => apssvJ_measurable r w
    have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
    have h_e_cont : Continuous (fun s : ℝ => e ((k : ℝ) * s / (2 : ℝ) ^ r)) := by
      unfold e; exact Complex.continuous_exp.comp (by continuity)
    have h_meas_summand : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) :=
      fun w => by
        have h_J_real : Measurable (fun η : List Bool → Bool => (apssvJ η r w : ℝ)) :=
          h_natCast_real.comp (h_meas_J w)
        have h_c : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp h_J_real
        have h_Y : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp (h_meas_T w)
        exact Complex.measurable_re.comp (h_c.mul (h_Y.sub measurable_const))
    have h_meas_sum : Measurable (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) :=
      Finset.measurable_sum _ (fun w _ => h_meas_summand w)
    have h_meas_exp : Measurable (fun η : List Bool → Bool => Real.exp (t * (
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re))) :=
      Real.measurable_exp.comp (h_meas_sum.const_mul t)
    -- Bound: |∑_w Re(...)| ≤ 2^r · 2.
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (Real.exp (|t| * (2 * (2 : ℝ) ^ r))))
      h_meas_exp.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
    intro η
    have h_sum_abs_le : |∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re| ≤
        2 * (2 : ℝ) ^ r := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h_card : (Finset.univ : Finset (Fin r → Bool)).card = 2 ^ r := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have h_each : ∀ w ∈ (Finset.univ : Finset (Fin r → Bool)),
          |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re| ≤ 2 := by
        intro w _
        exact (Complex.abs_re_le_norm _).trans
          (apssvBlockSum_centered_summand_norm_le_two η P k w w)
      calc ∑ w, _ ≤ ∑ _w : Fin r → Bool, (2 : ℝ) := Finset.sum_le_sum h_each
        _ = (2 ^ r : ℕ) * 2 := by rw [Finset.sum_const, h_card, nsmul_eq_mul]
        _ = 2 * (2 : ℝ) ^ r := by push_cast; ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    set S : ℝ := ∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re with hS_def
    have h1 : t * S ≤ |t| * (2 * (2 : ℝ) ^ r) := by
      have h2 : t * S ≤ |t * S| := le_abs_self _
      rw [abs_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left h_sum_abs_le (abs_nonneg _))
    exact h1
  · -- mgf_le: the main argument.
    -- Strategy: outer filter_upwards on Helper 1 (per-w c_w substitution) and
    -- Helper 2 (substitute joint integrand from κ(ω') to μ); then under μ,
    -- apply HasSubgaussianMGF.sum_of_iIndepFun.
    have hm_le : apssvShortSigma r ≤ MeasurableSpace.pi := apssvShortSigma_le r
    have hm'_le : apssvLongSigma r ≤ MeasurableSpace.pi := apssvLongSigma_le r
    set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η (fun _ : Fin r => false) P / (2 : ℝ) ^ r)
      ∂apssvEtaMeasure with hα_def
    -- α is invariant under w (apssvT_e_integral_w_invariant); we'll absorb later.
    -- Per-w c_w / Y_w setup.
    have h_c_meas_short : ∀ w : Fin r → Bool, @Measurable _ _ (apssvShortSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_c_apssvShortSigma_measurable r w k
    have h_Y_meas_long : ∀ w : Fin r → Bool, @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_Y_apssvLongSigma_measurable w P k
    have h_c_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => (h_c_meas_short w).mono hm_le le_rfl
    have h_Y_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => (h_Y_meas_long w).mono hm'_le le_rfl
    -- Re/Im of c_w bounded by 1, m-strongly-measurable (per w).
    have h_c_re_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re| ≤ 1 :=
      fun w η => (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_c_im_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im| ≤ 1 :=
      fun w η => (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_c_re_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re) :=
      fun w => ((Complex.measurable_re.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_c_im_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im) :=
      fun w => ((Complex.measurable_im.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    -- Helper 1 for each w (Re and Im).
    have h_re_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).re) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_re_meas_short w) (h_c_re_bd w)
    have h_im_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).im) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_im_meas_short w) (h_c_im_bd w)
    -- Combine Re and Im across all w via finite intersection.
    have h_c_eq_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun _ : List Bool → Bool =>
                e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)) := by
      rw [Filter.eventually_all]
      intro w
      filter_upwards [h_re_eq w, h_im_eq w] with ω' hre him
      filter_upwards [hre, him] with η hηre hηim
      exact Complex.ext hηre hηim
    -- α-invariance: ∫ Y_w' dμ = α for any w', via apssvT_e_integral_w_invariant.
    have h_α_inv : ∀ w : Fin r → Bool,
        (∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) = α := by
      intro w; exact apssvT_e_integral_w_invariant w (fun _ : Fin r => false) P k r
    -- Path X proper: kernel-level iIndepFun for Y_w → per-fiber Measure-level iIndepFun.
    -- Step 1: build Kernel.iIndepFun Y κ ν via Helper 3.
    have h_indep_long_short : ProbabilityTheory.Indep
        (apssvLongSigma r) (apssvShortSigma r) apssvEtaMeasure :=
      (apssv_short_long_indep r).symm
    have h_Y_iIndep_μ : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := apssvT_e_iIndepFun P r k
    have h_Y_kernel_iIndep : ProbabilityTheory.Kernel.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r))
        (apssvEtaMeasure.trim hm_le) :=
      iIndepFun_condExpKernel_of_indep_of_indep hm_le hm'_le
        h_indep_long_short h_Y_meas_long h_Y_iIndep_μ
    -- Step 2: apply Path X proper to extract per-fiber Measure-level iIndepFun.
    have h_Y_iIndep_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ProbabilityTheory.iIndepFun
          (fun w : Fin r → Bool => fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      Kernel.iIndepFun.iIndepFun_apply_ae h_Y_meas_top h_Y_kernel_iIndep
    -- Step 3: per-w κ(ω')-level mean-zero of Re(Y_w), Im(Y_w) via Helper 2.
    have h_Y_re_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_Y_re_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) := by
      intro w
      have h := (Complex.measurable_re.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_im_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) := by
      intro w
      have h := (Complex.measurable_im.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_int_Y_re_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_re_meas_long_strong w) (h_Y_re_int w)
    have h_int_Y_im_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_im_meas_long_strong w) (h_Y_im_int w)
    -- Combine per-w into ∀ᵐ ω', ∀ w.
    have h_int_Y_re_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_re_kernel
    have h_int_Y_im_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_im_kernel
    -- Outer filter_upwards: combine c_w-substitution + Y_w iIndepFun + per-w means.
    filter_upwards [h_c_eq_kernel, h_Y_iIndep_kernel,
      h_int_Y_re_kernel_all, h_int_Y_im_kernel_all] with
      ω' h_c_eq h_Y_iIndep_ω h_re_int_eq h_im_int_eq
    intro t
    -- Set z_w := c_w(ω').
    set Z : (Fin r → Bool) → ℂ := fun w =>
      e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r) with hZ_def
    have h_Z_norm : ∀ w, ‖Z w‖ = 1 := fun w => norm_e _
    -- κ(ω') is a probability measure.
    haveI h_κ_prob : MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r)) ω'
    -- Replace integrand: ∑_w Re(c_w(η)·(Y_w(η) - α)) ≡ ∑_w Re(Z_w·(Y_w(η) - α))
    -- on κ(ω') using h_c_eq.
    have h_X_eq_kernel :
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun η : List Bool → Bool =>
              ∑ w : Fin r → Bool,
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
      have h_each : ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool =>
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun η : List Bool → Bool =>
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
        intro w
        filter_upwards [h_c_eq w] with η hη
        rw [hη, h_α_inv w, hZ_def]
      -- Combine across all w (finite intersection).
      have h_all : ∀ᵐ η ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure
          (apssvShortSigma r) ω'),
          ∀ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re =
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re := by
        rw [Filter.eventually_all]; exact h_each
      filter_upwards [h_all] with η hη
      exact Finset.sum_congr rfl (fun w _ => hη w)
    -- mgf X (κ ω') t = ∫ exp(t · ∑_w Re(Z_w·(Y_w - α))) dκ(ω').
    have h_mgf_rewrite : ProbabilityTheory.mgf
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      unfold ProbabilityTheory.mgf
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_X_eq_kernel] with η hη; rw [hη]
    rw [h_mgf_rewrite]
    -- Path X strategy: build per-w HasSubgaussianMGF directly under κ(ω') via Hoeffding,
    -- then sum_of_iIndepFun (using Path X-derived iIndepFun (Y_w) under κ(ω')).
    --
    -- Per-w range bound (deterministic, holds under any measure).
    have h_per_w_range : ∀ w : Fin r → Bool, ∀ η : List Bool → Bool,
        |(Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re| ≤ 2 := by
      intro w η
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, h_Z_norm w, one_mul]
      refine (norm_sub_le _ _).trans ?_
      have h_Y : ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)‖ = 1 := norm_e _
      have h_α : ‖α‖ ≤ 1 := apssvT_e_integral_norm_le_one (fun _ : Fin r => false) P k r
      linarith
    -- Mean-zero of Re(Y_w), Im(Y_w) under μ (used to derive mean-zero under κ(ω') via Helper 2).
    have h_Y_int_μ_w : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := fun w => apssvT_e_integrable w P k r
    have h_int_Y_re_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure = α.re := by
      intro w
      show ∫ η, RCLike.re (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.re
      rw [integral_re (h_Y_int_μ_w w), h_α_inv w]; rfl
    have h_int_Y_im_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure = α.im := by
      intro w
      show ∫ η, RCLike.im (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.im
      rw [integral_im (h_Y_int_μ_w w), h_α_inv w]; rfl
    -- Per-w mean-zero under κ(ω'): derive from Helper 2 + decomposition of Re(Z_w · (Y_w - α)).
    -- κ(ω') is a probability measure (via h_κ_prob below).
    have h_per_w_mean_zero_kernel : ∀ w : Fin r → Bool,
        ∫ η, (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      intro w
      have h_decomp : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) := by
        intro η
        rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
            (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α) from by ring]
        rw [Complex.sub_re, Complex.mul_re, Complex.mul_re]; ring
      -- Integrability of Re(Y_w), Im(Y_w) under κ(ω') (bounded by 1 on probability measure).
      have h_Y_re_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (norm_e _).le
      have h_Y_im_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_im_le_norm _).trans (norm_e _).le
      have h_re_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_re_int_kernel.sub (MeasureTheory.integrable_const _)
      have h_im_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_im_int_kernel.sub (MeasureTheory.integrable_const _)
      -- Compute the integral.
      rw [show (fun η : List Bool → Bool => (Z w *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) =
          (fun η : List Bool → Bool =>
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)) from
        funext h_decomp]
      rw [MeasureTheory.integral_sub (h_re_diff_int.const_mul (Z w).re)
          (h_im_diff_int.const_mul (Z w).im),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_sub h_Y_re_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_sub h_Y_im_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      -- Now the integrals of Re(Y_w), Im(Y_w) under κ(ω') equal those under μ (Helper 2).
      rw [h_re_int_eq w, h_im_int_eq w, h_int_Y_re_μ w, h_int_Y_im_μ w]
      ring
    -- Per-w sub-Gaussian under κ(ω'): Hoeffding (range 2, mean 0) → param 1.
    have h_per_w_subg_kernel : ∀ w : Fin r → Bool,
        ProbabilityTheory.HasSubgaussianMGF
          (fun η : List Bool → Bool =>
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          1 (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      intro w
      set a : ℝ := -1 - (Z w * α).re with ha_def
      set b : ℝ := 1 - (Z w * α).re with hb_def
      have h_b_sub_a : b - a = 2 := by show (1 - (Z w * α).re) - (-1 - (Z w * α).re) = 2; ring
      have h_re_in_Icc : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re ∈ Set.Icc a b := by
        intro η
        have h_zY : |(Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re| ≤ 1 := by
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, h_Z_norm w, norm_e]; norm_num
        constructor
        · have h_eq : (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
              (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - (Z w * α).re := by
            rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
                Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α from by ring,
                Complex.sub_re]
          rw [h_eq, ha_def]
          linarith [neg_le_of_abs_le h_zY]
        · have h_eq : (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
              (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - (Z w * α).re := by
            rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
                Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α from by ring,
                Complex.sub_re]
          rw [h_eq, hb_def]
          linarith [le_of_abs_le h_zY]
      have h_re_meas : Measurable (fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) :=
        Complex.measurable_re.comp (((h_Y_meas_top w).sub_const α).const_mul (Z w))
      have h_subg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω')
        h_re_meas.aemeasurable
        (Filter.Eventually.of_forall h_re_in_Icc) (h_per_w_mean_zero_kernel w)
      have h_param_eq : ((‖b - a‖₊ / 2) ^ 2) = (1 : NNReal) := by
        ext; push_cast; rw [show b - a = 2 from h_b_sub_a]; norm_num
      rw [h_param_eq] at h_subg
      exact h_subg
    -- iIndepFun under κ(ω') of (η ↦ Re(Z_w · (Y_w(η) - α)))_w.
    -- Composition of h_Y_iIndep_ω with deterministic map y ↦ Re(Z_w · (y - α)).
    have h_iIndep_kernel : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h_φ_meas : ∀ w : Fin r → Bool, Measurable (fun y : ℂ => (Z w * (y - α)).re) :=
        fun w => Complex.measurable_re.comp ((measurable_id.sub_const α).const_mul (Z w))
      exact h_Y_iIndep_ω.comp (fun w : Fin r → Bool => fun y : ℂ => (Z w * (y - α)).re) h_φ_meas
    -- Apply HasSubgaussianMGF.sum_of_iIndepFun under κ(ω') to get sum sub-Gaussian.
    have h_sum_subg_kernel : ProbabilityTheory.HasSubgaussianMGF
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        (∑ _w : Fin r → Bool, (1 : NNReal))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
        (X := fun w η => (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        h_iIndep_kernel (s := Finset.univ) (c := fun _ => 1)
        (fun w _ => h_per_w_subg_kernel w)
      exact h
    -- Convert NNReal sum 2^r → real 2^r.
    have h_card_NN : (∑ _w : Fin r → Bool, (1 : NNReal)) = (2 : NNReal) ^ r := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    -- Conclude.
    have h_mgf_le := h_sum_subg_kernel.mgf_le t
    have h_mgf_def : ProbabilityTheory.mgf
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := rfl
    rw [h_mgf_def] at h_mgf_le
    rw [h_card_NN] at h_mgf_le
    exact h_mgf_le

/-- **Phase B aggregator (imaginary part)**: imaginary-part analog of
`apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum`.

The proof is structurally identical to the Re version, with `Complex.re` replaced by
`Complex.im` throughout. The sub-Gaussian range bound and per-w mean-zero argument
work identically (`|Im z| ≤ ‖z‖`, `Im(z·(Y-α)) = z.re·Im(Y-α) + z.im·Re(Y-α)`,
both Re(Y-α) and Im(Y-α) have mean 0 under μ). -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_summand_im_HasCondSubgaussianMGF_sum (P r k : ℕ) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
      ((2 : NNReal) ^ r) apssvEtaMeasure := by
  -- Structurally identical to the Re aggregator, with `.re` → `.im` throughout.
  -- The Im decomposition: (Z·(Y-α)).im = Z.re·Im(Y-α) + Z.im·Re(Y-α), so the same
  -- mean-zero argument works (Re(Y-α) and Im(Y-α) both mean-zero under κ(ω')).
  refine ⟨fun t => ?_, ?_⟩
  · rw [ProbabilityTheory.condExpKernel_comp_trim]
    have h_meas_T : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvT η w P) :=
      fun w => apssvT_measurable w P
    have h_meas_J : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvJ η r w) :=
      fun w => apssvJ_measurable r w
    have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
    have h_e_cont : Continuous (fun s : ℝ => e ((k : ℝ) * s / (2 : ℝ) ^ r)) := by
      unfold e; exact Complex.continuous_exp.comp (by continuity)
    have h_meas_summand : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im) :=
      fun w => by
        have h_J_real : Measurable (fun η : List Bool → Bool => (apssvJ η r w : ℝ)) :=
          h_natCast_real.comp (h_meas_J w)
        have h_c : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp h_J_real
        have h_Y : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp (h_meas_T w)
        exact Complex.measurable_im.comp (h_c.mul (h_Y.sub measurable_const))
    have h_meas_sum : Measurable (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im) :=
      Finset.measurable_sum _ (fun w _ => h_meas_summand w)
    have h_meas_exp : Measurable (fun η : List Bool → Bool => Real.exp (t * (
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im))) :=
      Real.measurable_exp.comp (h_meas_sum.const_mul t)
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (Real.exp (|t| * (2 * (2 : ℝ) ^ r))))
      h_meas_exp.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
    intro η
    have h_sum_abs_le : |∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im| ≤
        2 * (2 : ℝ) ^ r := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h_card : (Finset.univ : Finset (Fin r → Bool)).card = 2 ^ r := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have h_each : ∀ w ∈ (Finset.univ : Finset (Fin r → Bool)),
          |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im| ≤ 2 := by
        intro w _
        exact (Complex.abs_im_le_norm _).trans
          (apssvBlockSum_centered_summand_norm_le_two η P k w w)
      calc ∑ w, _ ≤ ∑ _w : Fin r → Bool, (2 : ℝ) := Finset.sum_le_sum h_each
        _ = (2 ^ r : ℕ) * 2 := by rw [Finset.sum_const, h_card, nsmul_eq_mul]
        _ = 2 * (2 : ℝ) ^ r := by push_cast; ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    set S : ℝ := ∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im with hS_def
    have h1 : t * S ≤ |t| * (2 * (2 : ℝ) ^ r) := by
      have h2 : t * S ≤ |t * S| := le_abs_self _
      rw [abs_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left h_sum_abs_le (abs_nonneg _))
    exact h1
  · -- mgf_le: Im version of the Re-aggregator argument.
    have hm_le : apssvShortSigma r ≤ MeasurableSpace.pi := apssvShortSigma_le r
    have hm'_le : apssvLongSigma r ≤ MeasurableSpace.pi := apssvLongSigma_le r
    set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η (fun _ : Fin r => false) P / (2 : ℝ) ^ r)
      ∂apssvEtaMeasure with hα_def
    have h_c_meas_short : ∀ w : Fin r → Bool, @Measurable _ _ (apssvShortSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_c_apssvShortSigma_measurable r w k
    have h_Y_meas_long : ∀ w : Fin r → Bool, @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_Y_apssvLongSigma_measurable w P k
    have h_c_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => (h_c_meas_short w).mono hm_le le_rfl
    have h_Y_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => (h_Y_meas_long w).mono hm'_le le_rfl
    have h_c_re_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re| ≤ 1 :=
      fun w η => (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_c_im_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im| ≤ 1 :=
      fun w η => (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_c_re_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re) :=
      fun w => ((Complex.measurable_re.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_c_im_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im) :=
      fun w => ((Complex.measurable_im.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_re_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).re) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_re_meas_short w) (h_c_re_bd w)
    have h_im_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).im) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_im_meas_short w) (h_c_im_bd w)
    have h_c_eq_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun _ : List Bool → Bool =>
                e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)) := by
      rw [Filter.eventually_all]
      intro w
      filter_upwards [h_re_eq w, h_im_eq w] with ω' hre him
      filter_upwards [hre, him] with η hηre hηim
      exact Complex.ext hηre hηim
    have h_α_inv : ∀ w : Fin r → Bool,
        (∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) = α := by
      intro w; exact apssvT_e_integral_w_invariant w (fun _ : Fin r => false) P k r
    -- Path X proper.
    have h_indep_long_short : ProbabilityTheory.Indep
        (apssvLongSigma r) (apssvShortSigma r) apssvEtaMeasure :=
      (apssv_short_long_indep r).symm
    have h_Y_iIndep_μ : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := apssvT_e_iIndepFun P r k
    have h_Y_kernel_iIndep : ProbabilityTheory.Kernel.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r))
        (apssvEtaMeasure.trim hm_le) :=
      iIndepFun_condExpKernel_of_indep_of_indep hm_le hm'_le
        h_indep_long_short h_Y_meas_long h_Y_iIndep_μ
    have h_Y_iIndep_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ProbabilityTheory.iIndepFun
          (fun w : Fin r → Bool => fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      Kernel.iIndepFun.iIndepFun_apply_ae h_Y_meas_top h_Y_kernel_iIndep
    -- Per-w κ(ω')-level mean of Re(Y_w), Im(Y_w) via Helper 2.
    have h_Y_re_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_Y_re_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) := by
      intro w
      have h := (Complex.measurable_re.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_im_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) := by
      intro w
      have h := (Complex.measurable_im.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_int_Y_re_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_re_meas_long_strong w) (h_Y_re_int w)
    have h_int_Y_im_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_im_meas_long_strong w) (h_Y_im_int w)
    have h_int_Y_re_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_re_kernel
    have h_int_Y_im_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_im_kernel
    filter_upwards [h_c_eq_kernel, h_Y_iIndep_kernel,
      h_int_Y_re_kernel_all, h_int_Y_im_kernel_all] with
      ω' h_c_eq h_Y_iIndep_ω h_re_int_eq h_im_int_eq
    intro t
    set Z : (Fin r → Bool) → ℂ := fun w =>
      e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r) with hZ_def
    have h_Z_norm : ∀ w, ‖Z w‖ = 1 := fun w => norm_e _
    haveI h_κ_prob : MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r)) ω'
    have h_X_eq_kernel :
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun η : List Bool → Bool =>
              ∑ w : Fin r → Bool,
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) := by
      have h_each : ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool =>
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun η : List Bool → Bool =>
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) := by
        intro w
        filter_upwards [h_c_eq w] with η hη
        rw [hη, h_α_inv w, hZ_def]
      have h_all : ∀ᵐ η ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure
          (apssvShortSigma r) ω'),
          ∀ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im =
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im := by
        rw [Filter.eventually_all]; exact h_each
      filter_upwards [h_all] with η hη
      exact Finset.sum_congr rfl (fun w _ => hη w)
    have h_mgf_rewrite : ProbabilityTheory.mgf
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      unfold ProbabilityTheory.mgf
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_X_eq_kernel] with η hη; rw [hη]
    rw [h_mgf_rewrite]
    -- Per-w range bound: |Im(Z_w · (Y_w - α))| ≤ 2.
    have h_per_w_range : ∀ w : Fin r → Bool, ∀ η : List Bool → Bool,
        |(Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im| ≤ 2 := by
      intro w η
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, h_Z_norm w, one_mul]
      refine (norm_sub_le _ _).trans ?_
      have h_Y : ‖e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)‖ = 1 := norm_e _
      have h_α : ‖α‖ ≤ 1 := apssvT_e_integral_norm_le_one (fun _ : Fin r => false) P k r
      linarith
    have h_Y_int_μ_w : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := fun w => apssvT_e_integrable w P k r
    have h_int_Y_re_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure = α.re := by
      intro w
      show ∫ η, RCLike.re (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.re
      rw [integral_re (h_Y_int_μ_w w), h_α_inv w]; rfl
    have h_int_Y_im_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure = α.im := by
      intro w
      show ∫ η, RCLike.im (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.im
      rw [integral_im (h_Y_int_μ_w w), h_α_inv w]; rfl
    -- Per-w mean-zero under κ(ω'): Im(Z_w · w) = Z.re · Im(w) + Z.im · Re(w).
    have h_per_w_mean_zero_kernel : ∀ w : Fin r → Bool,
        ∫ η, (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      intro w
      have h_decomp : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im =
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) +
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) := by
        intro η
        rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
            (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α) from by ring]
        rw [Complex.sub_im, Complex.mul_im, Complex.mul_im]; ring
      have h_Y_re_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (norm_e _).le
      have h_Y_im_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_im_le_norm _).trans (norm_e _).le
      have h_re_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_re_int_kernel.sub (MeasureTheory.integrable_const _)
      have h_im_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_im_int_kernel.sub (MeasureTheory.integrable_const _)
      rw [show (fun η : List Bool → Bool => (Z w *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) =
          (fun η : List Bool → Bool =>
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) +
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)) from
        funext h_decomp]
      rw [MeasureTheory.integral_add (h_im_diff_int.const_mul (Z w).re)
          (h_re_diff_int.const_mul (Z w).im),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_sub h_Y_im_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_sub h_Y_re_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      rw [h_re_int_eq w, h_im_int_eq w, h_int_Y_re_μ w, h_int_Y_im_μ w]
      ring
    -- Per-w sub-Gaussian under κ(ω'): Hoeffding (range 2, mean 0) → param 1.
    have h_per_w_subg_kernel : ∀ w : Fin r → Bool,
        ProbabilityTheory.HasSubgaussianMGF
          (fun η : List Bool → Bool =>
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
          1 (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      intro w
      set a : ℝ := -1 - (Z w * α).im with ha_def
      set b : ℝ := 1 - (Z w * α).im with hb_def
      have h_b_sub_a : b - a = 2 := by show (1 - (Z w * α).im) - (-1 - (Z w * α).im) = 2; ring
      have h_im_in_Icc : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im ∈ Set.Icc a b := by
        intro η
        have h_zY : |(Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im| ≤ 1 := by
          refine (Complex.abs_im_le_norm _).trans ?_
          rw [norm_mul, h_Z_norm w, norm_e]; norm_num
        constructor
        · have h_eq : (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im =
              (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - (Z w * α).im := by
            rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
                Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α from by ring,
                Complex.sub_im]
          rw [h_eq, ha_def]
          linarith [neg_le_of_abs_le h_zY]
        · have h_eq : (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im =
              (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - (Z w * α).im := by
            rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
                Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α from by ring,
                Complex.sub_im]
          rw [h_eq, hb_def]
          linarith [le_of_abs_le h_zY]
      have h_im_meas : Measurable (fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) :=
        Complex.measurable_im.comp (((h_Y_meas_top w).sub_const α).const_mul (Z w))
      have h_subg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω')
        h_im_meas.aemeasurable
        (Filter.Eventually.of_forall h_im_in_Icc) (h_per_w_mean_zero_kernel w)
      have h_param_eq : ((‖b - a‖₊ / 2) ^ 2) = (1 : NNReal) := by
        ext; push_cast; rw [show b - a = 2 from h_b_sub_a]; norm_num
      rw [h_param_eq] at h_subg
      exact h_subg
    have h_iIndep_kernel : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h_φ_meas : ∀ w : Fin r → Bool, Measurable (fun y : ℂ => (Z w * (y - α)).im) :=
        fun w => Complex.measurable_im.comp ((measurable_id.sub_const α).const_mul (Z w))
      exact h_Y_iIndep_ω.comp (fun w : Fin r → Bool => fun y : ℂ => (Z w * (y - α)).im) h_φ_meas
    have h_sum_subg_kernel : ProbabilityTheory.HasSubgaussianMGF
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        (∑ _w : Fin r → Bool, (1 : NNReal))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
        (X := fun w η => (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        h_iIndep_kernel (s := Finset.univ) (c := fun _ => 1)
        (fun w _ => h_per_w_subg_kernel w)
      exact h
    have h_card_NN : (∑ _w : Fin r → Bool, (1 : NNReal)) = (2 : NNReal) ^ r := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    have h_mgf_le := h_sum_subg_kernel.mgf_le t
    have h_mgf_def : ProbabilityTheory.mgf
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := rfl
    rw [h_mgf_def] at h_mgf_le
    rw [h_card_NN] at h_mgf_le
    exact h_mgf_le

/-- **Phase D aggregator (Re part, linear bound)**: the centered sum
`∑_w Re(c_w · (Y_w - α))` is conditionally sub-Gaussian wrt `apssvShortSigma r`
with parameter `16π²k²/2^r` (linear scaling).

Same chassis as `apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum`
(M=2), but using the sharper centered per-summand bound
`‖Z_w · (Y_w - α)‖ ≤ 4π·k/2^r` from `apssvBlockSum_centered_summand_norm_bound`.
Per-w Hoeffding gives sub-Gaussian param `(4π·k/2^r)² = 16π²k²/4^r`; sum over
`2^r` words yields `2^r · 16π²k²/4^r = 16π²k²/2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum_linear (P r k : ℕ) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      (Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r)) apssvEtaMeasure := by
  refine ⟨fun t => ?_, ?_⟩
  · -- Integrability follows as in the M=2 case; the norm-le-2 bound is still valid.
    rw [ProbabilityTheory.condExpKernel_comp_trim]
    have h_meas_T : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvT η w P) :=
      fun w => apssvT_measurable w P
    have h_meas_J : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvJ η r w) :=
      fun w => apssvJ_measurable r w
    have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
    have h_e_cont : Continuous (fun s : ℝ => e ((k : ℝ) * s / (2 : ℝ) ^ r)) := by
      unfold e; exact Complex.continuous_exp.comp (by continuity)
    have h_meas_summand : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) :=
      fun w => by
        have h_J_real : Measurable (fun η : List Bool → Bool => (apssvJ η r w : ℝ)) :=
          h_natCast_real.comp (h_meas_J w)
        have h_c : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp h_J_real
        have h_Y : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp (h_meas_T w)
        exact Complex.measurable_re.comp (h_c.mul (h_Y.sub measurable_const))
    have h_meas_sum : Measurable (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) :=
      Finset.measurable_sum _ (fun w _ => h_meas_summand w)
    have h_meas_exp : Measurable (fun η : List Bool → Bool => Real.exp (t * (
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re))) :=
      Real.measurable_exp.comp (h_meas_sum.const_mul t)
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (Real.exp (|t| * (2 * (2 : ℝ) ^ r))))
      h_meas_exp.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
    intro η
    have h_sum_abs_le : |∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re| ≤
        2 * (2 : ℝ) ^ r := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h_card : (Finset.univ : Finset (Fin r → Bool)).card = 2 ^ r := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have h_each : ∀ w ∈ (Finset.univ : Finset (Fin r → Bool)),
          |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re| ≤ 2 := by
        intro w _
        exact (Complex.abs_re_le_norm _).trans
          (apssvBlockSum_centered_summand_norm_le_two η P k w w)
      calc ∑ w, _ ≤ ∑ _w : Fin r → Bool, (2 : ℝ) := Finset.sum_le_sum h_each
        _ = (2 ^ r : ℕ) * 2 := by rw [Finset.sum_const, h_card, nsmul_eq_mul]
        _ = 2 * (2 : ℝ) ^ r := by push_cast; ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    set S : ℝ := ∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re with hS_def
    have h1 : t * S ≤ |t| * (2 * (2 : ℝ) ^ r) := by
      have h2 : t * S ≤ |t * S| := le_abs_self _
      rw [abs_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left h_sum_abs_le (abs_nonneg _))
    exact h1
  · -- mgf_le: linear chassis. Same Path X (Helper 1+2+iIndepFun) as M=2, but
    -- per-w Hoeffding range is `[0 - 4π·k/2^r, 0 + 4π·k/2^r]` (sharper) and the
    -- final sum NNReal is `Real.toNNReal (16π²k²/2^r)`.
    have hm_le : apssvShortSigma r ≤ MeasurableSpace.pi := apssvShortSigma_le r
    have hm'_le : apssvLongSigma r ≤ MeasurableSpace.pi := apssvLongSigma_le r
    set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η (fun _ : Fin r => false) P / (2 : ℝ) ^ r)
      ∂apssvEtaMeasure with hα_def
    have h_c_meas_short : ∀ w : Fin r → Bool, @Measurable _ _ (apssvShortSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_c_apssvShortSigma_measurable r w k
    have h_Y_meas_long : ∀ w : Fin r → Bool, @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_Y_apssvLongSigma_measurable w P k
    have h_c_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => (h_c_meas_short w).mono hm_le le_rfl
    have h_Y_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => (h_Y_meas_long w).mono hm'_le le_rfl
    have h_c_re_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re| ≤ 1 :=
      fun w η => (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_c_im_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im| ≤ 1 :=
      fun w η => (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_c_re_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re) :=
      fun w => ((Complex.measurable_re.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_c_im_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im) :=
      fun w => ((Complex.measurable_im.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_re_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).re) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_re_meas_short w) (h_c_re_bd w)
    have h_im_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).im) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_im_meas_short w) (h_c_im_bd w)
    have h_c_eq_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun _ : List Bool → Bool =>
                e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)) := by
      rw [Filter.eventually_all]
      intro w
      filter_upwards [h_re_eq w, h_im_eq w] with ω' hre him
      filter_upwards [hre, him] with η hηre hηim
      exact Complex.ext hηre hηim
    have h_α_inv : ∀ w : Fin r → Bool,
        (∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) = α := by
      intro w; exact apssvT_e_integral_w_invariant w (fun _ : Fin r => false) P k r
    have h_indep_long_short : ProbabilityTheory.Indep
        (apssvLongSigma r) (apssvShortSigma r) apssvEtaMeasure :=
      (apssv_short_long_indep r).symm
    have h_Y_iIndep_μ : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := apssvT_e_iIndepFun P r k
    have h_Y_kernel_iIndep : ProbabilityTheory.Kernel.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r))
        (apssvEtaMeasure.trim hm_le) :=
      iIndepFun_condExpKernel_of_indep_of_indep hm_le hm'_le
        h_indep_long_short h_Y_meas_long h_Y_iIndep_μ
    have h_Y_iIndep_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ProbabilityTheory.iIndepFun
          (fun w : Fin r → Bool => fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      Kernel.iIndepFun.iIndepFun_apply_ae h_Y_meas_top h_Y_kernel_iIndep
    have h_Y_re_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_Y_re_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) := by
      intro w
      have h := (Complex.measurable_re.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_im_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) := by
      intro w
      have h := (Complex.measurable_im.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_int_Y_re_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_re_meas_long_strong w) (h_Y_re_int w)
    have h_int_Y_im_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_im_meas_long_strong w) (h_Y_im_int w)
    have h_int_Y_re_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_re_kernel
    have h_int_Y_im_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_im_kernel
    filter_upwards [h_c_eq_kernel, h_Y_iIndep_kernel,
      h_int_Y_re_kernel_all, h_int_Y_im_kernel_all] with
      ω' h_c_eq h_Y_iIndep_ω h_re_int_eq h_im_int_eq
    intro t
    set Z : (Fin r → Bool) → ℂ := fun w =>
      e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r) with hZ_def
    have h_Z_norm : ∀ w, ‖Z w‖ = 1 := fun w => norm_e _
    haveI h_κ_prob : MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r)) ω'
    have h_X_eq_kernel :
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun η : List Bool → Bool =>
              ∑ w : Fin r → Bool,
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
      have h_each : ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool =>
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun η : List Bool → Bool =>
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) := by
        intro w
        filter_upwards [h_c_eq w] with η hη
        rw [hη, h_α_inv w, hZ_def]
      have h_all : ∀ᵐ η ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure
          (apssvShortSigma r) ω'),
          ∀ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re =
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re := by
        rw [Filter.eventually_all]; exact h_each
      filter_upwards [h_all] with η hη
      exact Finset.sum_congr rfl (fun w _ => hη w)
    have h_mgf_rewrite : ProbabilityTheory.mgf
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      unfold ProbabilityTheory.mgf
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_X_eq_kernel] with η hη; rw [hη]
    rw [h_mgf_rewrite]
    -- Per-w range bound (linear): |Re(Z_w · (Y_w - α))| ≤ 4π·k/2^r.
    set H : ℝ := 4 * Real.pi * (k : ℝ) / (2 : ℝ)^r with hH_def
    have h_H_nn : 0 ≤ H := by positivity
    have h_per_w_range : ∀ w : Fin r → Bool, ∀ η : List Bool → Bool,
        |(Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re| ≤ H := by
      intro w η
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, h_Z_norm w, one_mul]
      -- ‖Y - α‖ ≤ 4π·k/2^r from existing centered norm bound (using ‖e ‖ = 1).
      have h_existing : ‖e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)‖ ≤
          4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r :=
        apssvBlockSum_centered_summand_norm_bound η P k w (fun _ : Fin r => false)
      rw [norm_mul, norm_e, one_mul] at h_existing
      exact h_existing
    have h_Y_int_μ_w : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := fun w => apssvT_e_integrable w P k r
    have h_int_Y_re_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure = α.re := by
      intro w
      show ∫ η, RCLike.re (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.re
      rw [integral_re (h_Y_int_μ_w w), h_α_inv w]; rfl
    have h_int_Y_im_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure = α.im := by
      intro w
      show ∫ η, RCLike.im (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.im
      rw [integral_im (h_Y_int_μ_w w), h_α_inv w]; rfl
    have h_per_w_mean_zero_kernel : ∀ w : Fin r → Bool,
        ∫ η, (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      intro w
      have h_decomp : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re =
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) := by
        intro η
        rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
            (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α) from by ring]
        rw [Complex.sub_re, Complex.mul_re, Complex.mul_re]; ring
      have h_Y_re_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (norm_e _).le
      have h_Y_im_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_im_le_norm _).trans (norm_e _).le
      have h_re_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_re_int_kernel.sub (MeasureTheory.integrable_const _)
      have h_im_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_im_int_kernel.sub (MeasureTheory.integrable_const _)
      rw [show (fun η : List Bool → Bool => (Z w *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) =
          (fun η : List Bool → Bool =>
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) -
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)) from
        funext h_decomp]
      rw [MeasureTheory.integral_sub (h_re_diff_int.const_mul (Z w).re)
          (h_im_diff_int.const_mul (Z w).im),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_sub h_Y_re_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_sub h_Y_im_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      rw [h_re_int_eq w, h_im_int_eq w, h_int_Y_re_μ w, h_int_Y_im_μ w]
      ring
    -- Per-w sub-Gaussian under κ(ω'): Hoeffding (range [-H, H], mean 0) → param H².
    have h_per_w_subg_kernel : ∀ w : Fin r → Bool,
        ProbabilityTheory.HasSubgaussianMGF
          (fun η : List Bool → Bool =>
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          (Real.toNNReal (H^2))
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      intro w
      set a : ℝ := -H with ha_def
      set b : ℝ := H with hb_def
      have h_b_sub_a : b - a = 2 * H := by show H - (-H) = _; ring
      have h_re_in_Icc : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re ∈ Set.Icc a b := by
        intro η
        have h_abs := h_per_w_range w η
        constructor
        · rw [ha_def]; linarith [neg_le_of_abs_le h_abs]
        · rw [hb_def]; linarith [le_of_abs_le h_abs]
      have h_re_meas : Measurable (fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re) :=
        Complex.measurable_re.comp (((h_Y_meas_top w).sub_const α).const_mul (Z w))
      have h_subg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω')
        h_re_meas.aemeasurable
        (Filter.Eventually.of_forall h_re_in_Icc) (h_per_w_mean_zero_kernel w)
      have h_param_eq : ((‖b - a‖₊ / 2) ^ 2) = Real.toNNReal (H^2) := by
        ext
        push_cast
        rw [show b - a = 2 * H from h_b_sub_a]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * H)]
        rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ H^2)]
        ring
      rw [h_param_eq] at h_subg
      exact h_subg
    have h_iIndep_kernel : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h_φ_meas : ∀ w : Fin r → Bool, Measurable (fun y : ℂ => (Z w * (y - α)).re) :=
        fun w => Complex.measurable_re.comp ((measurable_id.sub_const α).const_mul (Z w))
      exact h_Y_iIndep_ω.comp (fun w : Fin r → Bool => fun y : ℂ => (Z w * (y - α)).re) h_φ_meas
    have h_sum_subg_kernel : ProbabilityTheory.HasSubgaussianMGF
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        (∑ _w : Fin r → Bool, Real.toNNReal (H^2))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
        (X := fun w η => (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        h_iIndep_kernel (s := Finset.univ) (c := fun _ => Real.toNNReal (H^2))
        (fun w _ => h_per_w_subg_kernel w)
      exact h
    -- Convert NNReal sum 2^r · H² → Real.toNNReal (16π²k²/2^r).
    have h_card_NN : (∑ _w : Fin r → Bool, Real.toNNReal (H^2)) =
        Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) := by
      rw [Finset.sum_const, Finset.card_univ]
      ext
      push_cast
      rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ H^2),
          Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤
            16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r)]
      simp only [hH_def]
      have h2r_pos : (0 : ℝ) < (2 : ℝ)^r := by positivity
      have h2r_ne : (2 : ℝ)^r ≠ 0 := ne_of_gt h2r_pos
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      -- Goal after push_cast: (2 : ℝ)^r * (4π·k/2^r)² = 16π²k²/2^r
      rw [div_pow,
          show (4 * Real.pi * (k : ℝ))^2 = 16 * Real.pi^2 * (k : ℝ)^2 from by ring,
          pow_two ((2 : ℝ)^r)]
      field_simp
    have h_mgf_le := h_sum_subg_kernel.mgf_le t
    have h_mgf_def : ProbabilityTheory.mgf
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).re)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := rfl
    rw [h_mgf_def] at h_mgf_le
    rw [h_card_NN] at h_mgf_le
    exact h_mgf_le

/-- **Phase D aggregator (Im part, linear bound)**: imaginary-part analog of
`apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum_linear`. Same chassis
with `Re` → `Im` throughout. -/
@[category API, AMS 11]
lemma apssvBlockSum_centered_summand_im_HasCondSubgaussianMGF_sum_linear (P r k : ℕ) :
    ProbabilityTheory.HasCondSubgaussianMGF (apssvShortSigma r) (apssvShortSigma_le r)
      (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
      (Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r)) apssvEtaMeasure := by
  refine ⟨fun t => ?_, ?_⟩
  · rw [ProbabilityTheory.condExpKernel_comp_trim]
    have h_meas_T : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvT η w P) :=
      fun w => apssvT_measurable w P
    have h_meas_J : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool => apssvJ η r w) :=
      fun w => apssvJ_measurable r w
    have h_natCast_real : Measurable ((↑) : ℕ → ℝ) := measurable_of_countable _
    have h_e_cont : Continuous (fun s : ℝ => e ((k : ℝ) * s / (2 : ℝ) ^ r)) := by
      unfold e; exact Complex.continuous_exp.comp (by continuity)
    have h_meas_summand : ∀ w : Fin r → Bool,
        Measurable (fun η : List Bool → Bool =>
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im) :=
      fun w => by
        have h_J_real : Measurable (fun η : List Bool → Bool => (apssvJ η r w : ℝ)) :=
          h_natCast_real.comp (h_meas_J w)
        have h_c : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp h_J_real
        have h_Y : Measurable (fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) := h_e_cont.measurable.comp (h_meas_T w)
        exact Complex.measurable_im.comp (h_c.mul (h_Y.sub measurable_const))
    have h_meas_sum : Measurable (fun η : List Bool → Bool =>
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im) :=
      Finset.measurable_sum _ (fun w _ => h_meas_summand w)
    have h_meas_exp : Measurable (fun η : List Bool → Bool => Real.exp (t * (
        ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im))) :=
      Real.measurable_exp.comp (h_meas_sum.const_mul t)
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (Real.exp (|t| * (2 * (2 : ℝ) ^ r))))
      h_meas_exp.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
    intro η
    have h_sum_abs_le : |∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im| ≤
        2 * (2 : ℝ) ^ r := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h_card : (Finset.univ : Finset (Fin r → Bool)).card = 2 ^ r := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have h_each : ∀ w ∈ (Finset.univ : Finset (Fin r → Bool)),
          |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im| ≤ 2 := by
        intro w _
        exact (Complex.abs_im_le_norm _).trans
          (apssvBlockSum_centered_summand_norm_le_two η P k w w)
      calc ∑ w, _ ≤ ∑ _w : Fin r → Bool, (2 : ℝ) := Finset.sum_le_sum h_each
        _ = (2 ^ r : ℕ) * 2 := by rw [Finset.sum_const, h_card, nsmul_eq_mul]
        _ = 2 * (2 : ℝ) ^ r := by push_cast; ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    set S : ℝ := ∑ w : Fin r → Bool, (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
        (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
          ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im with hS_def
    have h1 : t * S ≤ |t| * (2 * (2 : ℝ) ^ r) := by
      have h2 : t * S ≤ |t * S| := le_abs_self _
      rw [abs_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left h_sum_abs_le (abs_nonneg _))
    exact h1
  · -- mgf_le: Im version of the linear chassis.
    have hm_le : apssvShortSigma r ≤ MeasurableSpace.pi := apssvShortSigma_le r
    have hm'_le : apssvLongSigma r ≤ MeasurableSpace.pi := apssvLongSigma_le r
    set α : ℂ := ∫ η, e ((k : ℝ) * apssvT η (fun _ : Fin r => false) P / (2 : ℝ) ^ r)
      ∂apssvEtaMeasure with hα_def
    have h_c_meas_short : ∀ w : Fin r → Bool, @Measurable _ _ (apssvShortSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_c_apssvShortSigma_measurable r w k
    have h_Y_meas_long : ∀ w : Fin r → Bool, @Measurable _ _ (apssvLongSigma r) _
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => apssvBlockSum_Y_apssvLongSigma_measurable w P k
    have h_c_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)) :=
      fun w => (h_c_meas_short w).mono hm_le le_rfl
    have h_Y_meas_top : ∀ w : Fin r → Bool, Measurable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) :=
      fun w => (h_Y_meas_long w).mono hm'_le le_rfl
    have h_c_re_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re| ≤ 1 :=
      fun w η => (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_c_im_bd : ∀ w η, |(e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im| ≤ 1 :=
      fun w η => (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_c_re_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re) :=
      fun w => ((Complex.measurable_re.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_c_im_meas_short : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvShortSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im) :=
      fun w => ((Complex.measurable_im.comp (h_c_meas_short w) :
        @Measurable _ _ (apssvShortSigma r) _ _)).stronglyMeasurable
    have h_re_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).re)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).re) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_re_meas_short w) (h_c_re_bd w)
    have h_im_eq : ∀ w : Fin r → Bool, ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r)).im)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun _ : List Bool → Bool =>
              (e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)).im) :=
      fun w => condExpKernel_ae_eq_const_of_stronglyMeasurable_bounded
        (μ := apssvEtaMeasure) hm_le (h_c_im_meas_short w) (h_c_im_bd w)
    have h_c_eq_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool => e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r))
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun _ : List Bool → Bool =>
                e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r)) := by
      rw [Filter.eventually_all]
      intro w
      filter_upwards [h_re_eq w, h_im_eq w] with ω' hre him
      filter_upwards [hre, him] with η hηre hηim
      exact Complex.ext hηre hηim
    have h_α_inv : ∀ w : Fin r → Bool,
        (∫ η, e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) = α := by
      intro w; exact apssvT_e_integral_w_invariant w (fun _ : Fin r => false) P k r
    have h_indep_long_short : ProbabilityTheory.Indep
        (apssvLongSigma r) (apssvShortSigma r) apssvEtaMeasure :=
      (apssv_short_long_indep r).symm
    have h_Y_iIndep_μ : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := apssvT_e_iIndepFun P r k
    have h_Y_kernel_iIndep : ProbabilityTheory.Kernel.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r))
        (apssvEtaMeasure.trim hm_le) :=
      iIndepFun_condExpKernel_of_indep_of_indep hm_le hm'_le
        h_indep_long_short h_Y_meas_long h_Y_iIndep_μ
    have h_Y_iIndep_kernel : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ProbabilityTheory.iIndepFun
          (fun w : Fin r → Bool => fun η : List Bool → Bool =>
            e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      Kernel.iIndepFun.iIndepFun_apply_ae h_Y_meas_top h_Y_kernel_iIndep
    have h_Y_re_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_e _).le
    have h_Y_im_int : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
        apssvEtaMeasure := by
      intro w
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
        (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
        (MeasureTheory.ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (norm_e _).le
    have h_Y_re_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re) := by
      intro w
      have h := (Complex.measurable_re.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_Y_im_meas_long_strong : ∀ w : Fin r → Bool,
        @MeasureTheory.StronglyMeasurable _ _ _ (apssvLongSigma r)
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im) := by
      intro w
      have h := (Complex.measurable_im.comp (h_Y_meas_long w) :
        @Measurable _ _ (apssvLongSigma r) _ _)
      exact h.stronglyMeasurable
    have h_int_Y_re_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_re_meas_long_strong w) (h_Y_re_int w)
    have h_int_Y_im_kernel : ∀ w : Fin r → Bool,
        ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure :=
      fun w => integral_condExpKernel_of_indep
        (μ := apssvEtaMeasure) hm_le hm'_le h_indep_long_short
        (h_Y_im_meas_long_strong w) (h_Y_im_int w)
    have h_int_Y_re_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_re_kernel
    have h_int_Y_im_kernel_all : ∀ᵐ ω' ∂(apssvEtaMeasure.trim hm_le),
        ∀ w : Fin r → Bool,
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im
            ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') =
          ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure := by
      rw [Filter.eventually_all]; exact h_int_Y_im_kernel
    filter_upwards [h_c_eq_kernel, h_Y_iIndep_kernel,
      h_int_Y_re_kernel_all, h_int_Y_im_kernel_all] with
      ω' h_c_eq h_Y_iIndep_ω h_re_int_eq h_im_int_eq
    intro t
    set Z : (Fin r → Bool) → ℂ := fun w =>
      e ((k : ℝ) * apssvJ ω' r w / (2 : ℝ) ^ r) with hZ_def
    have h_Z_norm : ∀ w, ‖Z w‖ = 1 := fun w => norm_e _
    haveI h_κ_prob : MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
        (κ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r)) ω'
    have h_X_eq_kernel :
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
          =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
            (fun η : List Bool → Bool =>
              ∑ w : Fin r → Bool,
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) := by
      have h_each : ∀ w : Fin r → Bool,
          (fun η : List Bool → Bool =>
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
            =ᵐ[ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω']
              (fun η : List Bool → Bool =>
                (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) := by
        intro w
        filter_upwards [h_c_eq w] with η hη
        rw [hη, h_α_inv w, hZ_def]
      have h_all : ∀ᵐ η ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure
          (apssvShortSigma r) ω'),
          ∀ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im =
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im := by
        rw [Filter.eventually_all]; exact h_each
      filter_upwards [h_all] with η hη
      exact Finset.sum_congr rfl (fun w _ => hη w)
    have h_mgf_rewrite : ProbabilityTheory.mgf
        (fun η : List Bool → Bool =>
          ∑ w : Fin r → Bool,
            (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
              (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
                ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      unfold ProbabilityTheory.mgf
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_X_eq_kernel] with η hη; rw [hη]
    rw [h_mgf_rewrite]
    set H : ℝ := 4 * Real.pi * (k : ℝ) / (2 : ℝ)^r with hH_def
    have h_H_nn : 0 ≤ H := by positivity
    -- Per-w range bound (linear): |Im(Z_w · (Y_w - α))| ≤ 4π·k/2^r.
    have h_per_w_range : ∀ w : Fin r → Bool, ∀ η : List Bool → Bool,
        |(Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im| ≤ H := by
      intro w η
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, h_Z_norm w, one_mul]
      have h_existing : ‖e ((k : ℝ) * (apssvJ η r w : ℝ) / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)‖ ≤
          4 * Real.pi * (k : ℝ) / (2 : ℝ) ^ r :=
        apssvBlockSum_centered_summand_norm_bound η P k w (fun _ : Fin r => false)
      rw [norm_mul, norm_e, one_mul] at h_existing
      exact h_existing
    have h_Y_int_μ_w : ∀ w : Fin r → Bool, MeasureTheory.Integrable
        (fun η : List Bool → Bool => e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r))
        apssvEtaMeasure := fun w => apssvT_e_integrable w P k r
    have h_int_Y_re_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re ∂apssvEtaMeasure = α.re := by
      intro w
      show ∫ η, RCLike.re (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.re
      rw [integral_re (h_Y_int_μ_w w), h_α_inv w]; rfl
    have h_int_Y_im_μ : ∀ w : Fin r → Bool,
        ∫ η, (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im ∂apssvEtaMeasure = α.im := by
      intro w
      show ∫ η, RCLike.im (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)) ∂apssvEtaMeasure = α.im
      rw [integral_im (h_Y_int_μ_w w), h_α_inv w]; rfl
    have h_per_w_mean_zero_kernel : ∀ w : Fin r → Bool,
        ∫ η, (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') = 0 := by
      intro w
      have h_decomp : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im =
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) +
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re) := by
        intro η
        rw [show Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α) =
            (Z w * e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - Z w * α) from by ring]
        rw [Complex.sub_im, Complex.mul_im, Complex.mul_im]; ring
      have h_Y_re_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_re.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (norm_e _).le
      have h_Y_im_int_kernel : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
        refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
          (Complex.measurable_im.comp (h_Y_meas_top w)).aestronglyMeasurable
          (MeasureTheory.ae_of_all _ (fun η => ?_))
        rw [Real.norm_eq_abs]
        exact (Complex.abs_im_le_norm _).trans (norm_e _).le
      have h_re_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_re_int_kernel.sub (MeasureTheory.integrable_const _)
      have h_im_diff_int : MeasureTheory.Integrable
          (fun η : List Bool → Bool => (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im)
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') :=
        h_Y_im_int_kernel.sub (MeasureTheory.integrable_const _)
      rw [show (fun η : List Bool → Bool => (Z w *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) =
          (fun η : List Bool → Bool =>
            (Z w).re * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).im - α.im) +
            (Z w).im * ((e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r)).re - α.re)) from
        funext h_decomp]
      rw [MeasureTheory.integral_add (h_im_diff_int.const_mul (Z w).re)
          (h_re_diff_int.const_mul (Z w).im),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_sub h_Y_im_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_sub h_Y_re_int_kernel (MeasureTheory.integrable_const _),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      rw [h_re_int_eq w, h_im_int_eq w, h_int_Y_re_μ w, h_int_Y_im_μ w]
      ring
    have h_per_w_subg_kernel : ∀ w : Fin r → Bool,
        ProbabilityTheory.HasSubgaussianMGF
          (fun η : List Bool → Bool =>
            (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
          (Real.toNNReal (H^2))
          (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      intro w
      set a : ℝ := -H with ha_def
      set b : ℝ := H with hb_def
      have h_b_sub_a : b - a = 2 * H := by show H - (-H) = _; ring
      have h_im_in_Icc : ∀ η : List Bool → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im ∈ Set.Icc a b := by
        intro η
        have h_abs := h_per_w_range w η
        constructor
        · rw [ha_def]; linarith [neg_le_of_abs_le h_abs]
        · rw [hb_def]; linarith [le_of_abs_le h_abs]
      have h_im_meas : Measurable (fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im) :=
        Complex.measurable_im.comp (((h_Y_meas_top w).sub_const α).const_mul (Z w))
      have h_subg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω')
        h_im_meas.aemeasurable
        (Filter.Eventually.of_forall h_im_in_Icc) (h_per_w_mean_zero_kernel w)
      have h_param_eq : ((‖b - a‖₊ / 2) ^ 2) = Real.toNNReal (H^2) := by
        ext
        push_cast
        rw [show b - a = 2 * H from h_b_sub_a]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * H)]
        rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ H^2)]
        ring
      rw [h_param_eq] at h_subg
      exact h_subg
    have h_iIndep_kernel : ProbabilityTheory.iIndepFun
        (fun w : Fin r → Bool => fun η : List Bool → Bool =>
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h_φ_meas : ∀ w : Fin r → Bool, Measurable (fun y : ℂ => (Z w * (y - α)).im) :=
        fun w => Complex.measurable_im.comp ((measurable_id.sub_const α).const_mul (Z w))
      exact h_Y_iIndep_ω.comp (fun w : Fin r → Bool => fun y : ℂ => (Z w * (y - α)).im) h_φ_meas
    have h_sum_subg_kernel : ProbabilityTheory.HasSubgaussianMGF
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        (∑ _w : Fin r → Bool, Real.toNNReal (H^2))
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := by
      have h := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
        (X := fun w η => (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        h_iIndep_kernel (s := Finset.univ) (c := fun _ => Real.toNNReal (H^2))
        (fun w _ => h_per_w_subg_kernel w)
      exact h
    have h_card_NN : (∑ _w : Fin r → Bool, Real.toNNReal (H^2)) =
        Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) := by
      rw [Finset.sum_const, Finset.card_univ]
      ext
      push_cast
      rw [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ H^2),
          Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤
            16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r)]
      simp only [hH_def]
      have h2r_pos : (0 : ℝ) < (2 : ℝ)^r := by positivity
      have h2r_ne : (2 : ℝ)^r ≠ 0 := ne_of_gt h2r_pos
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [div_pow,
          show (4 * Real.pi * (k : ℝ))^2 = 16 * Real.pi^2 * (k : ℝ)^2 from by ring,
          pow_two ((2 : ℝ)^r)]
      field_simp
    have h_mgf_le := h_sum_subg_kernel.mgf_le t
    have h_mgf_def : ProbabilityTheory.mgf
        (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
        (ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') t =
        ∫ η, Real.exp (t * ∑ w : Fin r → Bool,
          (Z w * (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) - α)).im)
          ∂(ProbabilityTheory.condExpKernel apssvEtaMeasure (apssvShortSigma r) ω') := rfl
    rw [h_mgf_def] at h_mgf_le
    rw [h_card_NN] at h_mgf_le
    exact h_mgf_le

/-- **MGF bound for `Re B` (M=2 parameter)**: for any `t : ℝ`,
$$ \int \exp(t \cdot \text{Re B}(\eta)) \,d\eta \le \exp\!\left(2^r \cdot t^2 / 2\right). $$

**Proof**: combine the centered decomposition `Re B = ∑_w Re Z_w`
(`apssvBlockSum_re_eq_centered_sum` for `k ≥ 1`) with the Phase B aggregator
`apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum`, then apply the
tower lift `HasSubgaussianMGF_add_of_HasCondSubgaussianMGF` (with `X = 0`,
`cX = 0`) to obtain `HasSubgaussianMGF (Re B) (2^r) μ`, whose `mgf_le` field
delivers the claim. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_mgf_le_M2 (P r k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ProbabilityTheory.mgf
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).re)
      apssvEtaMeasure t ≤
      Real.exp (((2 : NNReal) ^ r : ℝ) * t^2 / 2) := by
  -- Reference word w₀ for the centered decomposition (any choice works since α is
  -- w-invariant under apssvEtaMeasure, but we pick w_w := w to align with the
  -- per-w lemma's signature).
  -- Step 1: rewrite Re B as ∑_w Re Z_w using the centered decomposition.
  have h_decomp : (fun η : List Bool → Bool => (apssvBlockSum η P r k).re) =
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) := by
    funext η
    -- Pick a default reference word w₀ for `apssvBlockSum_re_eq_centered_sum`.
    -- Since α is w-invariant, replacing the integral's `w₀` by each `w` in the sum
    -- body yields a per-summand identity.
    -- For r = 0, `Fin 0 → Bool` is uniquely the empty function; for r > 0, take const false.
    let w₀ : Fin r → Bool := fun _ => false
    have h_α_invariant : ∀ w : Fin r → Bool,
        (∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) =
        (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) :=
      fun w => apssvT_e_integral_w_invariant w w₀ P k r
    rw [apssvBlockSum_re_eq_centered_sum η P k hk w₀]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← h_α_invariant w]
  -- Step 2: build HasSubgaussianMGF from HasCondSubgaussianMGF via tower lift
  -- (with X = 0, cX = 0).
  have h_cond := apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum P r k
  -- HasSubgaussianMGF (0 : Ω → ℝ) 0 (μ.trim hm) via trim of the unconditional zero.
  have h_zero_uncond : ProbabilityTheory.HasSubgaussianMGF
      (fun _ : List Bool → Bool => (0 : ℝ)) 0 apssvEtaMeasure :=
    ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have h_zero : ProbabilityTheory.HasSubgaussianMGF (fun _ : List Bool → Bool => (0 : ℝ)) 0
      (apssvEtaMeasure.trim (apssvShortSigma_le r)) :=
    h_zero_uncond.trim (apssvShortSigma_le r) measurable_const
  -- Tower lift: HasSubgaussianMGF (0 + Y) (0 + 2^r) μ = HasSubgaussianMGF Y 2^r μ.
  have h_sum := ProbabilityTheory.HasSubgaussianMGF_add_of_HasCondSubgaussianMGF
    (apssvShortSigma_le r) h_zero h_cond
  -- Apply mgf_le.
  rw [h_decomp]
  have h_mgf_le := h_sum.mgf_le t
  -- Convert: ((fun _ => 0) + Y) η = Y η pointwise, so the mgf is the same.
  have h_mgf_eq : ProbabilityTheory.mgf
      ((fun _ : List Bool → Bool => (0 : ℝ)) +
        fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      apssvEtaMeasure t =
      ProbabilityTheory.mgf
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      apssvEtaMeasure t := by
    refine ProbabilityTheory.mgf_congr (Filter.Eventually.of_forall ?_)
    intro η; simp [Pi.add_apply]
  rw [h_mgf_eq] at h_mgf_le
  refine h_mgf_le.trans ?_
  refine Real.exp_le_exp.mpr ?_
  have h_param_eq : ((0 + (2 : NNReal) ^ r : NNReal) : ℝ) = ((2 : NNReal) ^ r : ℝ) := by
    push_cast; ring
  rw [h_param_eq]

/-- **MGF bound for `Im B` (M=2 parameter)**: imaginary-part analog of
`apssvBlockSum_re_mgf_le_M2`. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_mgf_le_M2 (P r k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ProbabilityTheory.mgf
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).im)
      apssvEtaMeasure t ≤
      Real.exp (((2 : NNReal) ^ r : ℝ) * t^2 / 2) := by
  have h_decomp : (fun η : List Bool → Bool => (apssvBlockSum η P r k).im) =
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im) := by
    funext η
    let w₀ : Fin r → Bool := fun _ => false
    have h_α_invariant : ∀ w : Fin r → Bool,
        (∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) =
        (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) :=
      fun w => apssvT_e_integral_w_invariant w w₀ P k r
    rw [apssvBlockSum_im_eq_centered_sum η P k hk w₀]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← h_α_invariant w]
  have h_cond := apssvBlockSum_centered_summand_im_HasCondSubgaussianMGF_sum P r k
  have h_zero_uncond : ProbabilityTheory.HasSubgaussianMGF
      (fun _ : List Bool → Bool => (0 : ℝ)) 0 apssvEtaMeasure :=
    ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have h_zero : ProbabilityTheory.HasSubgaussianMGF (fun _ : List Bool → Bool => (0 : ℝ)) 0
      (apssvEtaMeasure.trim (apssvShortSigma_le r)) :=
    h_zero_uncond.trim (apssvShortSigma_le r) measurable_const
  have h_sum := ProbabilityTheory.HasSubgaussianMGF_add_of_HasCondSubgaussianMGF
    (apssvShortSigma_le r) h_zero h_cond
  rw [h_decomp]
  have h_mgf_le := h_sum.mgf_le t
  have h_mgf_eq : ProbabilityTheory.mgf
      ((fun _ : List Bool → Bool => (0 : ℝ)) +
        fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
      apssvEtaMeasure t =
      ProbabilityTheory.mgf
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
      apssvEtaMeasure t := by
    refine ProbabilityTheory.mgf_congr (Filter.Eventually.of_forall ?_)
    intro η; simp [Pi.add_apply]
  rw [h_mgf_eq] at h_mgf_le
  refine h_mgf_le.trans ?_
  refine Real.exp_le_exp.mpr ?_
  have : ((0 + (2 : NNReal) ^ r : NNReal) : ℝ) = ((2 : NNReal) ^ r : ℝ) := by
    push_cast; ring
  rw [this]

/-- **Sub-Gaussian property of `Re B` (M=2 bound)**: combines the integrability
helper `apssvBlockSum_re_integrable_exp_mul` with the MGF bound
`apssvBlockSum_re_mgf_le_M2` to produce the `HasSubgaussianMGF` structure
with parameter `2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_hasSubgaussianMGF_M2 (P r k : ℕ) (hk : 1 ≤ k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).re)
      ((2 : NNReal) ^ r) apssvEtaMeasure where
  integrable_exp_mul := apssvBlockSum_re_integrable_exp_mul P r k
  mgf_le := apssvBlockSum_re_mgf_le_M2 P r k hk

/-- **Sub-Gaussian property of `Im B` (M=2 bound)**: imaginary-part analog. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_hasSubgaussianMGF_M2 (P r k : ℕ) (hk : 1 ≤ k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).im)
      ((2 : NNReal) ^ r) apssvEtaMeasure where
  integrable_exp_mul := apssvBlockSum_im_integrable_exp_mul P r k
  mgf_le := apssvBlockSum_im_mgf_le_M2 P r k hk

/-- **Sub-Gaussian tail (trivial M=2 bound)**: for any `k ≥ 1`, `t > 0`,
$$ \mu\{\eta : \|B_{P, r}(k)\| \ge t\} \le 4 \cdot \exp\!\left(-\frac{t^2}{16 \cdot 2^r}\right). $$

Outer derivation, *fully closed* modulo the conditional MGF claims
`apssvBlockSum_re_hasSubgaussianMGF_M2` and `apssvBlockSum_im_hasSubgaussianMGF_M2`:

1. **Set inclusion**: `‖B‖² = Re² + Im² ≥ t² ⟹ |Re B| ≥ t/√2 ∨ |Im B| ≥ t/√2`.
   Four events: `Re B ≥ t/√2`, `-Re B ≥ t/√2`, `Im B ≥ t/√2`, `-Im B ≥ t/√2`.

2. **Tail per event**: `HasSubgaussianMGF.measure_ge_le` gives each
   `μ{X ≥ t/√2} ≤ exp(-(t/√2)²/(2·2^r)) = exp(-t²/(4·2^r))`.

3. **Union**: total `≤ 4·exp(-t²/(4·2^r)) ≤ 4·exp(-t²/(16·2^r))`. -/
@[category API, AMS 11]
lemma apssvBlockSum_subGaussian_tail_M2 (P r k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) :
    (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      4 * Real.exp (-(t^2) / (16 * (2 : ℝ)^r)) := by
  -- Sub-Gaussian properties of Re B, Im B, -Re B, -Im B (param 2^r).
  have hRe := apssvBlockSum_re_hasSubgaussianMGF_M2 P r k hk
  have hIm := apssvBlockSum_im_hasSubgaussianMGF_M2 P r k hk
  have hReNeg := hRe.neg
  have hImNeg := hIm.neg
  -- Set up `s := t / √2`.
  set s : ℝ := t / Real.sqrt 2 with hs_def
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs_pos : 0 < s := div_pos ht h_sqrt2_pos
  have hs_nn : 0 ≤ s := hs_pos.le
  have h_s_sq : s ^ 2 = t ^ 2 / 2 := by
    rw [hs_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  -- Helper: from |X|² ≥ s² (and s ≥ 0) conclude s ≤ |X|.
  have h_abs_from_sq : ∀ X : ℝ, s ^ 2 ≤ X ^ 2 → s ≤ |X| := by
    intro X hX
    have h_sqrt_le : Real.sqrt (s^2) ≤ Real.sqrt (X^2) := Real.sqrt_le_sqrt hX
    rwa [Real.sqrt_sq hs_nn, Real.sqrt_sq_eq_abs] at h_sqrt_le
  -- Set inclusion: ‖B‖ ≥ t ⟹ one of the four events.
  have h_subset :
      {η : List Bool → Bool | t ≤ ‖apssvBlockSum η P r k‖} ⊆
      {η | s ≤ (apssvBlockSum η P r k).re} ∪
        ({η | s ≤ -(apssvBlockSum η P r k).re} ∪
          ({η | s ≤ (apssvBlockSum η P r k).im} ∪
           {η | s ≤ -(apssvBlockSum η P r k).im})) := by
    intro η hη
    -- ‖B‖ ≥ t ⟹ ‖B‖² ≥ t² ⟹ Re² + Im² ≥ t² ⟹ Re² ≥ s² ∨ Im² ≥ s².
    have h_norm_sq_ge : t ^ 2 ≤ ‖apssvBlockSum η P r k‖ ^ 2 :=
      pow_le_pow_left₀ ht.le hη 2
    have h_norm_sq_eq : ‖apssvBlockSum η P r k‖ ^ 2 =
        (apssvBlockSum η P r k).re ^ 2 + (apssvBlockSum η P r k).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [h_norm_sq_eq] at h_norm_sq_ge
    -- One of Re² or Im² ≥ s² (= t²/2).
    have h_max : s ^ 2 ≤ (apssvBlockSum η P r k).re ^ 2 ∨
                 s ^ 2 ≤ (apssvBlockSum η P r k).im ^ 2 := by
      by_contra h_neg
      push_neg at h_neg
      have : s ^ 2 + s ^ 2 = t ^ 2 := by rw [h_s_sq]; ring
      linarith [h_neg.1, h_neg.2]
    rcases h_max with h_re_sq | h_im_sq
    · -- Re² ≥ s² ⟹ |Re| ≥ s ⟹ Re ≥ s ∨ -Re ≥ s.
      rcases le_abs.mp (h_abs_from_sq _ h_re_sq) with h_pos | h_neg
      · left; exact h_pos
      · right; left; exact h_neg
    · rcases le_abs.mp (h_abs_from_sq _ h_im_sq) with h_pos | h_neg
      · right; right; left; exact h_pos
      · right; right; right; exact h_neg
  -- Apply measure_mono and finite-union bound (4 events).
  have h_meas_le : (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      apssvEtaMeasure.real {η | s ≤ (apssvBlockSum η P r k).re} +
      (apssvEtaMeasure.real {η | s ≤ -(apssvBlockSum η P r k).re} +
       (apssvEtaMeasure.real {η | s ≤ (apssvBlockSum η P r k).im} +
        apssvEtaMeasure.real {η | s ≤ -(apssvBlockSum η P r k).im})) := by
    have h_mono := MeasureTheory.measureReal_mono (μ := apssvEtaMeasure) h_subset
      (by finiteness)
    have h1 := MeasureTheory.measureReal_union_le
      (μ := apssvEtaMeasure)
      ({η | s ≤ (apssvBlockSum η P r k).re})
      ({η | s ≤ -(apssvBlockSum η P r k).re} ∪
       ({η | s ≤ (apssvBlockSum η P r k).im} ∪
        {η | s ≤ -(apssvBlockSum η P r k).im}))
    have h2 := MeasureTheory.measureReal_union_le
      (μ := apssvEtaMeasure)
      ({η | s ≤ -(apssvBlockSum η P r k).re})
      ({η | s ≤ (apssvBlockSum η P r k).im} ∪
       {η | s ≤ -(apssvBlockSum η P r k).im})
    have h3 := MeasureTheory.measureReal_union_le
      (μ := apssvEtaMeasure)
      ({η | s ≤ (apssvBlockSum η P r k).im})
      ({η | s ≤ -(apssvBlockSum η P r k).im})
    -- The goal uses .toReal on the measure; convert via defEq.
    show apssvEtaMeasure.real {η | t ≤ ‖apssvBlockSum η P r k‖} ≤ _
    linarith [h_mono]
  -- Each event bounded by exp(-s²/(2·2^r)) = exp(-t²/(4·2^r)) via sub-Gaussian.
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have h_param_eq : ((2 : NNReal) ^ r : ℝ) = (2 : ℝ) ^ r := by push_cast; rfl
  have h_re_bd := hRe.measure_ge_le hs_nn
  have h_im_bd := hIm.measure_ge_le hs_nn
  have h_reneg_bd := hReNeg.measure_ge_le hs_nn
  have h_imneg_bd := hImNeg.measure_ge_le hs_nn
  -- Convert exp arg: -s²/(2·(2^r : NNReal)) = -t²/(4·2^r).
  have h_exp_arg : -s ^ 2 / (2 * ((2 : NNReal) ^ r : ℝ)) =
      -(t ^ 2) / (4 * (2 : ℝ) ^ r) := by
    rw [h_param_eq, h_s_sq]
    field_simp
    ring
  -- Now sum the 4 bounds.
  have h_sum_le : (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      4 * Real.exp (-(t^2) / (4 * (2 : ℝ)^r)) := by
    refine h_meas_le.trans ?_
    have key : ∀ X : (List Bool → Bool) → ℝ,
        apssvEtaMeasure.real {η | s ≤ X η} ≤
          Real.exp (-s ^ 2 / (2 * ((2 : NNReal) ^ r : ℝ))) →
        apssvEtaMeasure.real {η | s ≤ X η} ≤
          Real.exp (-(t ^ 2) / (4 * (2 : ℝ) ^ r)) := by
      intro X hX
      rw [← h_exp_arg]; exact hX
    have hRe' := key _ h_re_bd
    have hIm' := key _ h_im_bd
    have hReNeg' := key _ h_reneg_bd
    have hImNeg' := key _ h_imneg_bd
    -- {η | s ≤ -X η} = {η | s ≤ (-X) η} (definitional).
    have h_eq_re_neg : apssvEtaMeasure.real
        {η | s ≤ -(apssvBlockSum η P r k).re} =
        apssvEtaMeasure.real {η | s ≤ (-(fun η => (apssvBlockSum η P r k).re)) η} := by
      rfl
    have h_eq_im_neg : apssvEtaMeasure.real
        {η | s ≤ -(apssvBlockSum η P r k).im} =
        apssvEtaMeasure.real {η | s ≤ (-(fun η => (apssvBlockSum η P r k).im)) η} := by
      rfl
    rw [h_eq_re_neg, h_eq_im_neg]
    linarith [hRe', hIm', hReNeg', hImNeg']
  -- Weaken denom from 4 to 16: 1/16 ≤ 1/4.
  refine h_sum_le.trans ?_
  have h_arg_le : -(t^2) / (4 * (2 : ℝ)^r) ≤ -(t^2) / (16 * (2 : ℝ)^r) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg t, h_2pow_pos]
  have h_exp_le : Real.exp (-(t^2) / (4 * (2 : ℝ)^r)) ≤
      Real.exp (-(t^2) / (16 * (2 : ℝ)^r)) :=
    Real.exp_le_exp.mpr h_arg_le
  linarith

/-- **MGF bound for `Re B` (linear parameter)**: for any `t : ℝ`,
$$ \int \exp(t \cdot \text{Re B}(\eta)) \,d\eta \le
   \exp\!\left(16 \pi^2 k^2 / 2^r \cdot t^2 / 2\right). $$

Same conditional MGF chassis as `apssvBlockSum_re_mgf_le_M2`, but using the
sharper centered per-summand bound `|c_w · (Y_w - α)| ≤ 4π·k/2^r` (from
`apssvBlockSum_centered_summand_norm_bound`). Hoeffding's lemma per `w` gives
per-summand sub-Gaussian param `(4π·k/2^r)² = 16π²k²/2^(2r)`; sum over `2^r`
gives `16π²k²/2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_mgf_le_linear (P r k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ProbabilityTheory.mgf
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).re)
      apssvEtaMeasure t ≤
      Real.exp ((Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) : ℝ) *
        t^2 / 2) := by
  -- Same chassis as apssvBlockSum_re_mgf_le_M2, but with the linear aggregator.
  have h_decomp : (fun η : List Bool → Bool => (apssvBlockSum η P r k).re) =
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re) := by
    funext η
    let w₀ : Fin r → Bool := fun _ => false
    have h_α_invariant : ∀ w : Fin r → Bool,
        (∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) =
        (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) :=
      fun w => apssvT_e_integral_w_invariant w w₀ P k r
    rw [apssvBlockSum_re_eq_centered_sum η P k hk w₀]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← h_α_invariant w]
  have h_cond := apssvBlockSum_centered_summand_HasCondSubgaussianMGF_sum_linear P r k
  have h_zero_uncond : ProbabilityTheory.HasSubgaussianMGF
      (fun _ : List Bool → Bool => (0 : ℝ)) 0 apssvEtaMeasure :=
    ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have h_zero : ProbabilityTheory.HasSubgaussianMGF (fun _ : List Bool → Bool => (0 : ℝ)) 0
      (apssvEtaMeasure.trim (apssvShortSigma_le r)) :=
    h_zero_uncond.trim (apssvShortSigma_le r) measurable_const
  have h_sum := ProbabilityTheory.HasSubgaussianMGF_add_of_HasCondSubgaussianMGF
    (apssvShortSigma_le r) h_zero h_cond
  rw [h_decomp]
  have h_mgf_le := h_sum.mgf_le t
  have h_mgf_eq : ProbabilityTheory.mgf
      ((fun _ : List Bool → Bool => (0 : ℝ)) +
        fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      apssvEtaMeasure t =
      ProbabilityTheory.mgf
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).re)
      apssvEtaMeasure t := by
    refine ProbabilityTheory.mgf_congr (Filter.Eventually.of_forall ?_)
    intro η; simp [Pi.add_apply]
  rw [h_mgf_eq] at h_mgf_le
  refine h_mgf_le.trans ?_
  refine Real.exp_le_exp.mpr ?_
  have h_param_eq : ((0 + Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) :
      NNReal) : ℝ) =
      ((Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) : NNReal) : ℝ) := by
    push_cast; ring
  rw [h_param_eq]

/-- **MGF bound for `Im B` (linear parameter)**: imaginary-part analog of
`apssvBlockSum_re_mgf_le_linear`. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_mgf_le_linear (P r k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ProbabilityTheory.mgf
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).im)
      apssvEtaMeasure t ≤
      Real.exp ((Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) : ℝ) *
        t^2 / 2) := by
  have h_decomp : (fun η : List Bool → Bool => (apssvBlockSum η P r k).im) =
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im) := by
    funext η
    let w₀ : Fin r → Bool := fun _ => false
    have h_α_invariant : ∀ w : Fin r → Bool,
        (∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) =
        (∫ η', e ((k : ℝ) * apssvT η' w₀ P / (2 : ℝ) ^ r) ∂apssvEtaMeasure) :=
      fun w => apssvT_e_integral_w_invariant w w₀ P k r
    rw [apssvBlockSum_im_eq_centered_sum η P k hk w₀]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← h_α_invariant w]
  have h_cond := apssvBlockSum_centered_summand_im_HasCondSubgaussianMGF_sum_linear P r k
  have h_zero_uncond : ProbabilityTheory.HasSubgaussianMGF
      (fun _ : List Bool → Bool => (0 : ℝ)) 0 apssvEtaMeasure :=
    ProbabilityTheory.HasSubgaussianMGF.fun_zero
  have h_zero : ProbabilityTheory.HasSubgaussianMGF (fun _ : List Bool → Bool => (0 : ℝ)) 0
      (apssvEtaMeasure.trim (apssvShortSigma_le r)) :=
    h_zero_uncond.trim (apssvShortSigma_le r) measurable_const
  have h_sum := ProbabilityTheory.HasSubgaussianMGF_add_of_HasCondSubgaussianMGF
    (apssvShortSigma_le r) h_zero h_cond
  rw [h_decomp]
  have h_mgf_le := h_sum.mgf_le t
  have h_mgf_eq : ProbabilityTheory.mgf
      ((fun _ : List Bool → Bool => (0 : ℝ)) +
        fun η : List Bool → Bool => ∑ w : Fin r → Bool,
          (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
            (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
              ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
      apssvEtaMeasure t =
      ProbabilityTheory.mgf
      (fun η : List Bool → Bool => ∑ w : Fin r → Bool,
        (e ((k : ℝ) * apssvJ η r w / (2 : ℝ) ^ r) *
          (e ((k : ℝ) * apssvT η w P / (2 : ℝ) ^ r) -
            ∫ η', e ((k : ℝ) * apssvT η' w P / (2 : ℝ) ^ r) ∂apssvEtaMeasure)).im)
      apssvEtaMeasure t := by
    refine ProbabilityTheory.mgf_congr (Filter.Eventually.of_forall ?_)
    intro η; simp [Pi.add_apply]
  rw [h_mgf_eq] at h_mgf_le
  refine h_mgf_le.trans ?_
  refine Real.exp_le_exp.mpr ?_
  have h_param_eq : ((0 + Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) :
      NNReal) : ℝ) =
      ((Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) : NNReal) : ℝ) := by
    push_cast; ring
  rw [h_param_eq]

/-- **Sub-Gaussian property of `Re B` (linear bound)**: combines the
integrability helper with the MGF bound to produce the `HasSubgaussianMGF`
structure with parameter `16π²k²/2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_re_hasSubgaussianMGF_linear (P r k : ℕ) (hk : 1 ≤ k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).re)
      (Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r)) apssvEtaMeasure where
  integrable_exp_mul := apssvBlockSum_re_integrable_exp_mul P r k
  mgf_le := apssvBlockSum_re_mgf_le_linear P r k hk

/-- **Sub-Gaussian property of `Im B` (linear bound)**: imaginary-part analog. -/
@[category API, AMS 11]
lemma apssvBlockSum_im_hasSubgaussianMGF_linear (P r k : ℕ) (hk : 1 ≤ k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun η : List Bool → Bool => (apssvBlockSum η P r k).im)
      (Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r)) apssvEtaMeasure where
  integrable_exp_mul := apssvBlockSum_im_integrable_exp_mul P r k
  mgf_le := apssvBlockSum_im_mgf_le_linear P r k hk

/-- **Sub-Gaussian tail (linear M = 4π·k/2^r bound)**: for any `k ≥ 1`,
`t > 0`,
$$ \mu\{\eta : \|B_{P, r}(k)\| \ge t\} \le 4 \cdot \exp\!\left(-\frac{t^2 \cdot 2^r}
   {64 \pi^2 k^2}\right). $$

**Use**: tight in the *long-block* regime `r ≥ b(k)` where `2^r ≫ k` makes
this bound dominate `apssvBlockSum_subGaussian_tail_M2`.

Outer derivation, *fully closed* modulo the conditional MGF claims
`apssvBlockSum_re/im_hasSubgaussianMGF_linear`. Same union/tail chain as
`apssvBlockSum_subGaussian_tail_M2` with sub-Gaussian parameter
`16π²k²/2^r` instead of `2^r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_subGaussian_tail_linear (P r k : ℕ) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0 < t) :
    (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      4 * Real.exp (-(t^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) := by
  -- Sub-Gaussian properties.
  have hRe := apssvBlockSum_re_hasSubgaussianMGF_linear P r k hk
  have hIm := apssvBlockSum_im_hasSubgaussianMGF_linear P r k hk
  have hReNeg := hRe.neg
  have hImNeg := hIm.neg
  -- s := t/√2.
  set s : ℝ := t / Real.sqrt 2 with hs_def
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs_pos : 0 < s := div_pos ht h_sqrt2_pos
  have hs_nn : 0 ≤ s := hs_pos.le
  have h_s_sq : s ^ 2 = t ^ 2 / 2 := by
    rw [hs_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  -- Helper: from |X|² ≥ s² (and s ≥ 0) conclude s ≤ |X|.
  have h_abs_from_sq : ∀ X : ℝ, s ^ 2 ≤ X ^ 2 → s ≤ |X| := by
    intro X hX
    have h_sqrt_le : Real.sqrt (s^2) ≤ Real.sqrt (X^2) := Real.sqrt_le_sqrt hX
    rwa [Real.sqrt_sq hs_nn, Real.sqrt_sq_eq_abs] at h_sqrt_le
  -- Set inclusion.
  have h_subset :
      {η : List Bool → Bool | t ≤ ‖apssvBlockSum η P r k‖} ⊆
      {η | s ≤ (apssvBlockSum η P r k).re} ∪
        ({η | s ≤ -(apssvBlockSum η P r k).re} ∪
          ({η | s ≤ (apssvBlockSum η P r k).im} ∪
           {η | s ≤ -(apssvBlockSum η P r k).im})) := by
    intro η hη
    have h_norm_sq_ge : t ^ 2 ≤ ‖apssvBlockSum η P r k‖ ^ 2 :=
      pow_le_pow_left₀ ht.le hη 2
    have h_norm_sq_eq : ‖apssvBlockSum η P r k‖ ^ 2 =
        (apssvBlockSum η P r k).re ^ 2 + (apssvBlockSum η P r k).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [h_norm_sq_eq] at h_norm_sq_ge
    have h_max : s ^ 2 ≤ (apssvBlockSum η P r k).re ^ 2 ∨
                 s ^ 2 ≤ (apssvBlockSum η P r k).im ^ 2 := by
      by_contra h_neg
      push_neg at h_neg
      have : s ^ 2 + s ^ 2 = t ^ 2 := by rw [h_s_sq]; ring
      linarith [h_neg.1, h_neg.2]
    rcases h_max with h_re_sq | h_im_sq
    · rcases le_abs.mp (h_abs_from_sq _ h_re_sq) with h_pos | h_neg
      · left; exact h_pos
      · right; left; exact h_neg
    · rcases le_abs.mp (h_abs_from_sq _ h_im_sq) with h_pos | h_neg
      · right; right; left; exact h_pos
      · right; right; right; exact h_neg
  -- Apply union bound.
  have h_meas_le : (apssvEtaMeasure {η | t ≤ ‖apssvBlockSum η P r k‖}).toReal ≤
      apssvEtaMeasure.real {η | s ≤ (apssvBlockSum η P r k).re} +
      (apssvEtaMeasure.real {η | s ≤ -(apssvBlockSum η P r k).re} +
       (apssvEtaMeasure.real {η | s ≤ (apssvBlockSum η P r k).im} +
        apssvEtaMeasure.real {η | s ≤ -(apssvBlockSum η P r k).im})) := by
    have h_mono := MeasureTheory.measureReal_mono (μ := apssvEtaMeasure) h_subset
      (by finiteness)
    have h1 := MeasureTheory.measureReal_union_le
      (μ := apssvEtaMeasure)
      ({η | s ≤ (apssvBlockSum η P r k).re})
      ({η | s ≤ -(apssvBlockSum η P r k).re} ∪
       ({η | s ≤ (apssvBlockSum η P r k).im} ∪
        {η | s ≤ -(apssvBlockSum η P r k).im}))
    have h2 := MeasureTheory.measureReal_union_le
      (μ := apssvEtaMeasure)
      ({η | s ≤ -(apssvBlockSum η P r k).re})
      ({η | s ≤ (apssvBlockSum η P r k).im} ∪
       {η | s ≤ -(apssvBlockSum η P r k).im})
    have h3 := MeasureTheory.measureReal_union_le
      (μ := apssvEtaMeasure)
      ({η | s ≤ (apssvBlockSum η P r k).im})
      ({η | s ≤ -(apssvBlockSum η P r k).im})
    show apssvEtaMeasure.real {η | t ≤ ‖apssvBlockSum η P r k‖} ≤ _
    linarith [h_mono]
  -- Each event bounded via sub-Gaussian.
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have h_param_nn : (0 : ℝ) ≤ 16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r := by positivity
  have h_param_eq :
      ((Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) : NNReal) : ℝ) =
      16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r := Real.coe_toNNReal _ h_param_nn
  have h_re_bd := hRe.measure_ge_le hs_nn
  have h_im_bd := hIm.measure_ge_le hs_nn
  have h_reneg_bd := hReNeg.measure_ge_le hs_nn
  have h_imneg_bd := hImNeg.measure_ge_le hs_nn
  -- Convert exp arg: -s²/(2·c) = -t²·2^r/(64π²k²).
  have h_exp_arg : -s ^ 2 /
      (2 * ((Real.toNNReal (16 * Real.pi^2 * (k : ℝ)^2 / (2 : ℝ)^r) : NNReal) : ℝ)) =
      -(t ^ 2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2) := by
    rw [h_param_eq, h_s_sq]
    field_simp
    ring
  refine h_meas_le.trans ?_
  have h_eq_re_neg :
      apssvEtaMeasure.real {η | s ≤ -(apssvBlockSum η P r k).re} =
      apssvEtaMeasure.real {η | s ≤ (-(fun η => (apssvBlockSum η P r k).re)) η} := rfl
  have h_eq_im_neg :
      apssvEtaMeasure.real {η | s ≤ -(apssvBlockSum η P r k).im} =
      apssvEtaMeasure.real {η | s ≤ (-(fun η => (apssvBlockSum η P r k).im)) η} := rfl
  rw [h_eq_re_neg, h_eq_im_neg]
  -- The 4 sub-Gaussian bounds.
  have h_re_bd' :
      apssvEtaMeasure.real {η | s ≤ (apssvBlockSum η P r k).re} ≤
      Real.exp (-(t^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) := by
    rw [← h_exp_arg]; exact h_re_bd
  have h_im_bd' :
      apssvEtaMeasure.real {η | s ≤ (apssvBlockSum η P r k).im} ≤
      Real.exp (-(t^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) := by
    rw [← h_exp_arg]; exact h_im_bd
  have h_reneg_bd' :
      apssvEtaMeasure.real
        {η | s ≤ (-(fun η => (apssvBlockSum η P r k).re)) η} ≤
      Real.exp (-(t^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) := by
    rw [← h_exp_arg]; exact h_reneg_bd
  have h_imneg_bd' :
      apssvEtaMeasure.real
        {η | s ≤ (-(fun η => (apssvBlockSum η P r k).im)) η} ≤
      Real.exp (-(t^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) := by
    rw [← h_exp_arg]; exact h_imneg_bd
  linarith

/-- **Universal-`P` sub-Gaussian tail (M = 2)**: combines residue reduction
(`apssvBlockSum_residue_measure_bound`) with the M=2 sub-Gaussian tail
(`apssvBlockSum_subGaussian_tail_M2`):
$$ \mu\{\eta : \exists P, \|B_{P, r}(k)\| > \tau\} \le 2^h \cdot 4 \cdot
   \exp\!\left(-\frac{\tau'^2}{16 \cdot 2^r}\right), $$
where `τ' := τ - 2π·k/2^h` (which we require to be positive). The factor
`2^h` accounts for the union over `Q < 2^h` after residue reduction.

**Use**: With `2^h` chosen so `τ' ≥ τ/2`, this gives an exp-summable bound
across `(k, r)` after the trivial-bound shortcut handles small `r`. -/
@[category API, AMS 11]
lemma apssvBlockSum_universalP_subGaussian_M2 (r k h : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h) :
    (apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖}).toReal ≤
      (2 : ℝ) ^ h * (4 * Real.exp
        (-(τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h)^2 / (16 * (2 : ℝ)^r))) := by
  set τ' : ℝ := τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h with hτ'_def
  -- Residue measure bound (ENNReal).
  have h_residue := apssvBlockSum_residue_measure_bound r k h τ
  -- Convert to real-valued bound on the sum.
  have h_finiteness : ∀ Q : ℕ,
      apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖} ≠ ⊤ := fun _ =>
    MeasureTheory.measure_ne_top _ _
  have h_residue_real :
      (apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖}).toReal ≤
      ∑ Q ∈ Finset.range (2 ^ h),
        (apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖}).toReal := by
    rw [← ENNReal.toReal_sum (fun Q _ => h_finiteness Q)]
    exact ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr (fun Q _ => h_finiteness Q)) h_residue
  -- Bound each term by sub-Gaussian tail with t = τ'.
  have h_per_term : ∀ Q : ℕ,
      (apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖}).toReal ≤
      4 * Real.exp (-(τ')^2 / (16 * (2 : ℝ)^r)) := by
    intro Q
    -- {τ' < ‖B‖} ⊆ {τ' ≤ ‖B‖}.
    have h_sub : {η : List Bool → Bool | τ' < ‖apssvBlockSum η Q r k‖} ⊆
        {η | τ' ≤ ‖apssvBlockSum η Q r k‖} :=
      Set.setOf_subset_setOf.mpr (fun _ hη => hη.le)
    have h_meas_sub :
        (apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖}).toReal ≤
        (apssvEtaMeasure {η | τ' ≤ ‖apssvBlockSum η Q r k‖}).toReal :=
      ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
        (MeasureTheory.measure_mono h_sub)
    exact h_meas_sub.trans
      (apssvBlockSum_subGaussian_tail_M2 Q r k hk τ' hτ_pos)
  refine h_residue_real.trans ?_
  refine (Finset.sum_le_sum fun Q _ => h_per_term Q).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; rfl

/-- **Universal-`P` sub-Gaussian tail (linear bound)**: same as
`apssvBlockSum_universalP_subGaussian_M2` but using the linear sub-Gaussian
tail `apssvBlockSum_subGaussian_tail_linear`:
$$ \mu\{\eta : \exists P, \|B_{P, r}(k)\| > \tau\} \le 2^h \cdot 4 \cdot
   \exp\!\left(-\frac{\tau'^2 \cdot 2^r}{64 \pi^2 k^2}\right). $$
Tight in the long-block regime `r ≥ b(k)`. -/
@[category API, AMS 11]
lemma apssvBlockSum_universalP_subGaussian_linear (r k h : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h) :
    (apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖}).toReal ≤
      (2 : ℝ) ^ h * (4 * Real.exp
        (-((τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h)^2 * (2 : ℝ)^r) /
         (64 * Real.pi^2 * (k : ℝ)^2))) := by
  set τ' : ℝ := τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h with hτ'_def
  have h_residue := apssvBlockSum_residue_measure_bound r k h τ
  have h_finiteness : ∀ Q : ℕ,
      apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖} ≠ ⊤ := fun _ =>
    MeasureTheory.measure_ne_top _ _
  have h_residue_real :
      (apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖}).toReal ≤
      ∑ Q ∈ Finset.range (2 ^ h),
        (apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖}).toReal := by
    rw [← ENNReal.toReal_sum (fun Q _ => h_finiteness Q)]
    exact ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr (fun Q _ => h_finiteness Q)) h_residue
  have h_per_term : ∀ Q : ℕ,
      (apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖}).toReal ≤
      4 * Real.exp (-((τ')^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) := by
    intro Q
    have h_sub : {η : List Bool → Bool | τ' < ‖apssvBlockSum η Q r k‖} ⊆
        {η | τ' ≤ ‖apssvBlockSum η Q r k‖} :=
      Set.setOf_subset_setOf.mpr (fun _ hη => hη.le)
    have h_meas_sub :
        (apssvEtaMeasure {η | τ' < ‖apssvBlockSum η Q r k‖}).toReal ≤
        (apssvEtaMeasure {η | τ' ≤ ‖apssvBlockSum η Q r k‖}).toReal :=
      ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
        (MeasureTheory.measure_mono h_sub)
    exact h_meas_sub.trans
      (apssvBlockSum_subGaussian_tail_linear Q r k hk τ' hτ_pos)
  refine h_residue_real.trans ?_
  refine (Finset.sum_le_sum fun Q _ => h_per_term Q).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; rfl

/- ## Bad-event measure decomposition + per-`(k, r)` ENNReal bounds

Reduce the universal bad event `{η | ¬ apssvBlockBound η C}` to a measurable
double tsum over `(k, r)` with the inner `P`-quantification absorbed by
residue reduction. Each `(k, r)`-summand admits one of three closed-form
ENNReal bounds (trivial, M=2 explicit, linear explicit, regime-split). -/

/-- **Bad event for `apssvBlockBound`**: the complement of `{η | apssvBlockBound η C}`
expressed as a countable union over `(k, P, r)` with `1 ≤ k`. Pure unfolding of
the universal definition + De Morgan. -/
@[category API, AMS 11]
lemma apssvBlockBound_compl_eq_iUnion (C : ℝ) :
    {η : List Bool → Bool | ¬ apssvBlockBound η C} =
      ⋃ k : ℕ, ⋃ (_ : 1 ≤ k),
      ⋃ r : ℕ, ⋃ P : ℕ,
        {η : List Bool → Bool |
          C * Real.sqrt ((r : ℝ) + apssvB k) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
          ‖apssvBlockSum η P r k‖} := by
  ext η
  unfold apssvBlockBound
  simp only [not_forall, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, P, r, hk, hbound⟩
    push_neg at hbound
    exact ⟨k, hk, r, P, hbound⟩
  · rintro ⟨k, hk, r, P, hbound⟩
    exact ⟨k, P, r, hk, by push_neg; exact hbound⟩

/-- **Measurability of `{η | apssvBlockBound η C}`**: a countable intersection
of measurable sets `{η | ‖B_{P, r}(k)‖ ≤ threshold}`. Each block-sum is
measurable in `η` (`apssvBlockSum_measurable`); the threshold is constant. -/
@[category API, AMS 11]
lemma apssvBlockBound_measurableSet (C : ℝ) :
    MeasurableSet {η : List Bool → Bool | apssvBlockBound η C} := by
  -- Rewrite the set as an intersection.
  have h_eq : {η : List Bool → Bool | apssvBlockBound η C} =
      ⋂ k : ℕ, ⋂ P : ℕ, ⋂ r : ℕ, ⋂ (_ : 1 ≤ k),
        {η | ‖apssvBlockSum η P r k‖ ≤
          C * Real.sqrt ((r : ℝ) + apssvB k) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))} := by
    ext η; unfold apssvBlockBound; simp
  rw [h_eq]
  refine MeasurableSet.iInter (fun k => ?_)
  refine MeasurableSet.iInter (fun P => ?_)
  refine MeasurableSet.iInter (fun r => ?_)
  refine MeasurableSet.iInter (fun _ => ?_)
  exact measurableSet_le (apssvBlockSum_measurable P r k).norm measurable_const

/-- **Bridge: `μ(bad) < 1 ⟹ 0 < μ(good)`** for `apssvBlockBound`.

On a probability measure, `μ(s) = 1 - μ(sᶜ)`, so `μ(sᶜ) < 1 ⟹ 0 < μ(s)`. Pure
measure-theoretic conversion using `MeasureTheory.prob_compl_eq_one_sub`. -/
@[category API, AMS 11]
lemma apssv_blockBound_pos_of_compl_lt_one {C : ℝ}
    (hC_meas : MeasurableSet {η : List Bool → Bool | apssvBlockBound η C})
    (h : apssvEtaMeasure {η : List Bool → Bool | ¬ apssvBlockBound η C} < 1) :
    0 < apssvEtaMeasure {η : List Bool → Bool | apssvBlockBound η C} := by
  have h_compl_eq :
      {η : List Bool → Bool | ¬ apssvBlockBound η C} =
      {η : List Bool → Bool | apssvBlockBound η C}ᶜ := by
    ext η; simp
  rw [h_compl_eq] at h
  rw [MeasureTheory.prob_compl_eq_one_sub hC_meas] at h
  -- h : 1 - μ S < 1
  -- ⟹ 0 < μ S (since μ S ≤ 1).
  have h_le_one := MeasureTheory.prob_le_one (μ := apssvEtaMeasure)
    (s := {η | apssvBlockBound η C})
  -- 1 - μ S < 1 ↔ μ S ≠ 0 (using μ S ≤ 1 < ⊤).
  by_contra h_zero
  push_neg at h_zero
  have h_eq_zero : apssvEtaMeasure {η | apssvBlockBound η C} = 0 :=
    le_antisymm h_zero bot_le
  rw [h_eq_zero] at h
  simp at h

/-- **Bad-event measure as a double tsum (with universal-`P` collapsing)**:
bounds the bad event by a double tsum over `(k, r)`, with the inner measure
being the universal-`P` event:
$$ \mu\{\eta : \lnot \mathrm{apssvBlockBound}\,\eta\,C\} \;\le\;
   \sum_{k} \sum_r \mu\{\eta : 1 \le k \land \exists P,
   \|B_{P, r}(k)\| > \tau\}. $$

The crucial step is *collapsing* the `P`-union before summing. Without this,
`∑'_P μ{‖B_P‖ > τ}` diverges (each term has the same bound, infinitely many
`P`s). The universal-`P` sub-Gaussian bounds then handle each
`μ{∃ P, ‖B_P‖ > τ}` finitely via residue reduction. -/
@[category API, AMS 11]
lemma apssv_blockBound_compl_measure_le_tsum_kr (C : ℝ) :
    apssvEtaMeasure {η : List Bool → Bool | ¬ apssvBlockBound η C} ≤
    ∑' k : ℕ, ∑' r : ℕ,
      apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
        C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2))
            ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
        ‖apssvBlockSum η P r k‖} := by
  -- Bad set ⊆ ⋃ k, ⋃ r, {η | 1 ≤ k ∧ ∃ P, ‖B_{P,r}(k)‖ > τ}
  have h_subset :
      {η : List Bool → Bool | ¬ apssvBlockBound η C} ⊆
      ⋃ k : ℕ, ⋃ r : ℕ,
        {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
          C * Real.sqrt ((r : ℝ) + apssvB k) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
          ‖apssvBlockSum η P r k‖} := by
    intro η hη
    unfold apssvBlockBound at hη
    push_neg at hη
    obtain ⟨k, P, r, hk, h⟩ := hη
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    exact ⟨hk, P, h⟩
  refine le_trans (MeasureTheory.measure_mono h_subset) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  exact MeasureTheory.measure_iUnion_le _

/-- **Per-`(k, r)` trivial regime**: when the threshold exceeds the
deterministic bound `‖B‖ ≤ 2^r`, the per-`(k, r)` bad-event measure is `0`.

Direct corollary of `apssvBlockSum_bad_event_eq_empty_of_two_pow_le`: the
universal-`P` bad event is the empty set, hence has measure `0`. -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_eq_zero_of_trivial (C : ℝ) (k r : ℕ)
    (h_trivial : (2 : ℝ) ^ r ≤
      C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) :
    apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
      ‖apssvBlockSum η P r k‖} = 0 := by
  -- {η | 1 ≤ k ∧ ∃ P, τ < ‖B_P‖} ⊆ {η | ∃ P, τ < ‖B_P‖} = ∅.
  have h_sub : {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
      ‖apssvBlockSum η P r k‖} ⊆
      {η : List Bool → Bool | ∃ P : ℕ,
        C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2))
            ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
        ‖apssvBlockSum η P r k‖} := by
    intro η hη; exact hη.2
  have h_empty :=
    apssvBlockSum_bad_event_eq_empty_of_two_pow_le (r := r) (k := k)
      (C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) h_trivial
  rw [show {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
      ‖apssvBlockSum η P r k‖} = ∅ from
    Set.eq_empty_of_subset_empty (h_empty ▸ h_sub)]
  exact MeasureTheory.measure_empty

/-- **Per-`(k, r)` sub-Gaussian regime (M=2 version)**: when the threshold is
*below* `2^r` (sub-Gaussian needed) and we pick reduction depth `h` so
`2π·k/2^h ≤ τ/2`, the per-`(k, r)` bad-event measure is bounded by
$$ 2^h \cdot 4 \cdot \exp\!\left(-\frac{\tau'^2}{16 \cdot 2^r}\right), $$
where `τ' = τ - 2π·k/2^h`.

Translates the real-valued universal-`P` sub-Gaussian bound
(`apssvBlockSum_universalP_subGaussian_M2`) back to an `ENNReal` measure
bound, ready to plug into the tsum summation. The `1 ≤ k` condition is
absorbed via subset inclusion. -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_M2 (k r h : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (τ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h) :
    apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal ((2 : ℝ) ^ h * (4 * Real.exp
      (-(τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h)^2 / (16 * (2 : ℝ)^r)))) := by
  -- Step 1: drop the `1 ≤ k` to a subset.
  have h_sub : {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} ⊆
      {η : List Bool → Bool | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} := fun _ hη => hη.2
  refine le_trans (MeasureTheory.measure_mono h_sub) ?_
  -- Step 2: convert .toReal bound to ENNReal bound.
  have h_real := apssvBlockSum_universalP_subGaussian_M2 r k h hk τ τ_pos
  have h_finite : apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have h_rhs_nn : (0 : ℝ) ≤ (2 : ℝ) ^ h * (4 * Real.exp
      (-(τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h)^2 / (16 * (2 : ℝ)^r))) := by
    positivity
  have h_eq := (ENNReal.ofReal_toReal h_finite).symm
  rw [h_eq]
  exact ENNReal.ofReal_le_ofReal h_real

/-- **Per-`(k, r)` sub-Gaussian regime (linear M = 4π·k/2^r version)**: same
shape as `apssv_per_kr_measure_le_M2` but using the linear-in-`k` sub-Gaussian
parameter (tight in the long-block regime `r ≥ b(k)`):
$$ \mu\{\eta : 1 \le k \land \exists P, \tau < \|B_{P, r}(k)\|\} \le
   2^h \cdot 4 \cdot \exp\!\left(-\frac{\tau'^2 \cdot 2^r}{64 \pi^2 k^2}\right). $$
-/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_linear (k r h : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (τ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h) :
    apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal ((2 : ℝ) ^ h * (4 * Real.exp
      (-((τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h)^2 * (2 : ℝ)^r) /
       (64 * Real.pi^2 * (k : ℝ)^2)))) := by
  have h_sub : {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} ⊆
      {η : List Bool → Bool | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} := fun _ hη => hη.2
  refine le_trans (MeasureTheory.measure_mono h_sub) ?_
  have h_real := apssvBlockSum_universalP_subGaussian_linear r k h hk τ τ_pos
  have h_finite : apssvEtaMeasure {η | ∃ P : ℕ, τ < ‖apssvBlockSum η P r k‖} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  rw [(ENNReal.ofReal_toReal h_finite).symm]
  exact ENNReal.ofReal_le_ofReal h_real

/-- **Monotonicity of the bad-event set in `C`**: as `C` increases, the bad
event `{η | ¬ apssvBlockBound η C}` shrinks (the threshold `τ(C, k, r)`
grows linearly in `C`, so fewer `η` violate the bound). -/
@[category API, AMS 11]
lemma apssv_blockBound_compl_antitone {C₁ C₂ : ℝ} (_hC : 0 ≤ C₁) (h : C₁ ≤ C₂) :
    {η : List Bool → Bool | ¬ apssvBlockBound η C₂} ⊆
    {η : List Bool → Bool | ¬ apssvBlockBound η C₁} := by
  intro η hη
  unfold apssvBlockBound at hη ⊢
  push_neg at hη ⊢
  obtain ⟨k, P, r, hk, hbound₂⟩ := hη
  refine ⟨k, P, r, hk, ?_⟩
  -- Threshold for C₁ ≤ threshold for C₂; use transitivity.
  have h_threshold_nn :
      0 ≤ Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) := by
    apply mul_nonneg (Real.sqrt_nonneg _) (le_min ?_ ?_)
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc C₁ * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))
      ≤ C₂ * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2))
            ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right h h_threshold_nn
    _ < ‖apssvBlockSum η P r k‖ := hbound₂

/-- **Existence of a residue depth `h`**: for any `(k, τ)` with `τ > 0`, there
exists `h : ℕ` such that `2π·k/2^h < τ/2`, i.e., the residue-shift condition
`0 < τ - 2π·k/2^h` holds.

Concrete choice: `h = ⌊log₂(4π·k/τ)⌋ + 1` (or any larger). This means picking
`h` such that `2^h > 4π·k/τ`, equivalently `2^h > 8π·k/(2τ)`, giving
`2π·k/2^h < τ/2`. -/
@[category API, AMS 11]
lemma apssv_exists_h_residue_shift (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ h : ℕ, 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by
  -- We want 2π·k/2^h < τ, equivalently 2^h > 2π·k/τ.
  -- Use `pow_unbounded_of_one_lt` or similar to find a large enough h.
  have h_target_pos : (0 : ℝ) ≤ 2 * Real.pi * (k : ℝ) / τ := by positivity
  obtain ⟨h, h_lt⟩ := pow_unbounded_of_one_lt (2 * Real.pi * (k : ℝ) / τ)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨h, ?_⟩
  -- 2π·k/2^h < τ from 2^h > 2π·k/τ.
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  rw [show (τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h) =
      ((τ * (2 : ℝ) ^ h - 2 * Real.pi * (k : ℝ)) / (2 : ℝ) ^ h) from by
    field_simp]
  rw [div_pos_iff]
  left
  refine ⟨?_, h_2pow_pos⟩
  -- 2^h > 2π·k/τ ⟹ τ·2^h > 2π·k.
  have h_prod : 2 * Real.pi * (k : ℝ) < τ * (2 : ℝ) ^ h := by
    rw [show 2 * Real.pi * (k : ℝ) = τ * (2 * Real.pi * (k : ℝ) / τ) from by
      field_simp]
    exact mul_lt_mul_of_pos_left h_lt hτ
  linarith

/-- **Strong residue-depth existence with explicit polynomial bound on `2^h`**:
strengthens `apssv_exists_h_residue_shift_half` by also bounding `2^h` from
above by an explicit polynomial in `k` and `1/τ`. This is what the summation
argument needs: with `2^h ≤ 8π·k/τ + 4`, the per-(k, r) prefactor becomes a
controllable function of (k, τ) rather than an unbounded existential.

Construction: let `c := 4π·k/τ`, `n := ⌈c⌉ + 1` (a positive natural with
`n > c`). Take `h := Nat.log 2 n + 1`. Then `n < 2^h ≤ 2n` from
`Nat.lt_pow_succ_log_self` and `Nat.pow_log_le_self`, and `n ≤ c + 2` from
`Nat.ceil_lt_add_one`, giving `2^h ≤ 2n ≤ 2c + 4 = 8π·k/τ + 4`. -/
@[category API, AMS 11]
lemma apssv_exists_h_residue_shift_strong (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ h : ℕ, τ / 2 ≤ τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h ∧
             (2 : ℝ) ^ h ≤ 8 * Real.pi * (k : ℝ) / τ + 4 := by
  set c : ℝ := 4 * Real.pi * (k : ℝ) / τ with hc_def
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have hc_nn : 0 ≤ c := by positivity
  set n : ℕ := Nat.ceil c + 1 with hn_def
  have hn_pos : 0 < n := Nat.succ_pos _
  have hn_ne_zero : n ≠ 0 := hn_pos.ne'
  -- Lower bound: c < n.
  have h_n_gt_c : c < (n : ℝ) := by
    have h_ceil_le : c ≤ ↑(Nat.ceil c) := Nat.le_ceil c
    push_cast [hn_def]
    linarith
  -- Upper bound: n ≤ c + 2.
  have h_n_le : (n : ℝ) ≤ c + 2 := by
    have h_ceil_lt : ↑(Nat.ceil c) < c + 1 := Nat.ceil_lt_add_one hc_nn
    push_cast [hn_def]
    linarith
  set h := Nat.log 2 n + 1 with hh_def
  refine ⟨h, ?_, ?_⟩
  · -- Show τ/2 ≤ τ - 2π·k/2^h, i.e., 2π·k/2^h ≤ τ/2, i.e., 4π·k ≤ τ·2^h.
    -- We have 2^h > n > c = 4π·k/τ, so τ·2^h > 4π·k, so 2π·k/2^h < τ/2.
    have h_lt_pow : n < 2 ^ h := by
      rw [hh_def, Nat.add_one]
      exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have h_lt_pow_real : (n : ℝ) < (2 : ℝ) ^ h := by exact_mod_cast h_lt_pow
    have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
    have h_c_lt_pow : c < (2 : ℝ) ^ h := lt_trans h_n_gt_c h_lt_pow_real
    -- c < 2^h ⟹ 4π·k < τ·2^h ⟹ 2π·k/2^h < τ/2.
    have h_4πk_lt : 4 * Real.pi * (k : ℝ) < τ * (2 : ℝ) ^ h := by
      have := (mul_lt_mul_of_pos_left h_c_lt_pow hτ)
      rw [show τ * c = 4 * Real.pi * (k : ℝ) from by
        rw [hc_def]; field_simp] at this
      exact this
    -- Now derive 2π·k/2^h ≤ τ/2.
    have : 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h ≤ τ / 2 := by
      rw [div_le_div_iff₀ h_2pow_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith
  · -- Show 2^h ≤ 8π·k/τ + 4 = 2c + 4 ≤ 2n + 2 (using n ≤ c+2 — wait, 2n ≤ 2c+4).
    -- 2^h ≤ 2n by Nat.pow_log_le_self.
    have h_pow_log_le : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn_ne_zero
    have h_pow_le : 2 ^ h ≤ 2 * n := by
      rw [hh_def]
      calc 2 ^ (Nat.log 2 n + 1)
          = 2 * 2 ^ Nat.log 2 n := by rw [pow_succ]; ring
        _ ≤ 2 * n := Nat.mul_le_mul_left 2 h_pow_log_le
    have h_pow_le_real : ((2 : ℕ) ^ h : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast h_pow_le
    have h_pow_eq : ((2 : ℕ) ^ h : ℝ) = (2 : ℝ) ^ h := by push_cast; rfl
    rw [← h_pow_eq]
    -- 2^h ≤ 2n ≤ 2·(c + 2) = 2c + 4 = 8π·k/τ + 4.
    have h_2n_le : 2 * (n : ℝ) ≤ 2 * (c + 2) := by linarith
    have h_2c_eq : 2 * c = 8 * Real.pi * (k : ℝ) / τ := by
      rw [hc_def]; ring
    linarith

/-- **Per-`(k, r)` sub-Gaussian bound (M=2) with explicit prefactor**: combines
`apssv_exists_h_residue_shift_strong` with `apssv_per_kr_measure_le_M2` to give
a per-`(k, r)` bound that is *fully closed-form* in `(k, r, τ)`, with no
existential `h`:
$$ \mu \le \left(\frac{8\pi k}{\tau} + 4\right) \cdot 4 \cdot \exp\!\left(-\frac{(\tau/2)^2}{16 \cdot 2^r}\right). $$
This is the form ready to plug into the tsum summation in
`apssv_exists_C_with_bad_event_lt_one`. -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_M2_explicit (k r : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal ((8 * Real.pi * (k : ℝ) / τ + 4) *
      (4 * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r)))) := by
  obtain ⟨h, h_half, h_pow_le⟩ := apssv_exists_h_residue_shift_strong k τ hτ
  have hτ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by linarith
  have h_M2 := apssv_per_kr_measure_le_M2 k r h hk τ hτ_pos
  refine h_M2.trans (ENNReal.ofReal_le_ofReal ?_)
  set τ' : ℝ := τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h with hτ'_def
  -- Goal: 2^h · 4·exp(-(τ')²/c) ≤ (8πk/τ + 4) · 4·exp(-(τ/2)²/c).
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have h_2pow_r_pos : (0 : ℝ) < 16 * (2 : ℝ) ^ r := by positivity
  have h_τ_half_pos : 0 < τ / 2 := by linarith
  -- (τ/2)² ≤ τ'².
  have h_τ_half_sq_le : (τ / 2)^2 ≤ τ'^2 := by
    apply sq_le_sq'
    · linarith
    · exact h_half
  -- exp(-(τ')²/c) ≤ exp(-(τ/2)²/c).
  have h_neg_le : -(τ')^2 / (16 * (2 : ℝ)^r) ≤ -(τ / 2)^2 / (16 * (2 : ℝ)^r) :=
    div_le_div_of_nonneg_right (by linarith) h_2pow_r_pos.le
  have h_exp_le : Real.exp (-(τ')^2 / (16 * (2 : ℝ)^r)) ≤
      Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r)) :=
    Real.exp_le_exp.mpr h_neg_le
  -- 4·exp(-(τ')²/c) ≤ 4·exp(-(τ/2)²/c).
  have h_4_exp_nn : 0 ≤ (4 : ℝ) * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r)) := by
    positivity
  have h_pow_le_real : (2 : ℝ) ^ h ≤ 8 * Real.pi * (k : ℝ) / τ + 4 := h_pow_le
  -- Chain: 2^h · A ≤ 2^h · B ≤ (8πk/τ + 4) · B.
  calc (2 : ℝ) ^ h * (4 * Real.exp (-(τ')^2 / (16 * (2 : ℝ)^r)))
      ≤ (2 : ℝ) ^ h * (4 * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_exp_le (by norm_num))
          h_2pow_pos.le
    _ ≤ (8 * Real.pi * (k : ℝ) / τ + 4) *
          (4 * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r))) :=
        mul_le_mul_of_nonneg_right h_pow_le_real h_4_exp_nn

/-- **Per-`(k, r)` sub-Gaussian bound (linear) with explicit prefactor**: linear
analog of `apssv_per_kr_measure_le_M2_explicit`:
$$ \mu \le \left(\frac{8\pi k}{\tau} + 4\right) \cdot 4 \cdot \exp\!\left(-\frac{(\tau/2)^2 \cdot 2^r}{64 \pi^2 k^2}\right). $$ -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_linear_explicit (k r : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal ((8 * Real.pi * (k : ℝ) / τ + 4) *
      (4 * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
        (64 * Real.pi^2 * (k : ℝ)^2)))) := by
  obtain ⟨h, h_half, h_pow_le⟩ := apssv_exists_h_residue_shift_strong k τ hτ
  have hτ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by linarith
  have h_lin := apssv_per_kr_measure_le_linear k r h hk τ hτ_pos
  refine h_lin.trans (ENNReal.ofReal_le_ofReal ?_)
  set τ' : ℝ := τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h with hτ'_def
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_denom_pos : (0 : ℝ) < 64 * Real.pi^2 * (k : ℝ)^2 := by positivity
  have h_τ_half_pos : 0 < τ / 2 := by linarith
  have h_τ_half_sq_le : (τ / 2)^2 ≤ τ'^2 := by
    apply sq_le_sq'
    · linarith
    · exact h_half
  have h_2pow_r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have h_mul_le : (τ / 2)^2 * (2 : ℝ)^r ≤ τ'^2 * (2 : ℝ)^r :=
    mul_le_mul_of_nonneg_right h_τ_half_sq_le h_2pow_r_pos.le
  have h_neg_le : -(τ'^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2) ≤
      -((τ / 2)^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2) :=
    div_le_div_of_nonneg_right (by linarith) h_denom_pos.le
  have h_exp_le : Real.exp (-(τ'^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) ≤
      Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) :=
    Real.exp_le_exp.mpr h_neg_le
  have h_4_exp_nn : 0 ≤ (4 : ℝ) * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
      (64 * Real.pi^2 * (k : ℝ)^2)) := by positivity
  have h_pow_le_real : (2 : ℝ) ^ h ≤ 8 * Real.pi * (k : ℝ) / τ + 4 := h_pow_le
  calc (2 : ℝ) ^ h * (4 * Real.exp (-(τ'^2 * (2 : ℝ)^r) /
        (64 * Real.pi^2 * (k : ℝ)^2)))
      ≤ (2 : ℝ) ^ h * (4 * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
          (64 * Real.pi^2 * (k : ℝ)^2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_exp_le (by norm_num))
          h_2pow_pos.le
    _ ≤ (8 * Real.pi * (k : ℝ) / τ + 4) *
          (4 * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
            (64 * Real.pi^2 * (k : ℝ)^2))) :=
        mul_le_mul_of_nonneg_right h_pow_le_real h_4_exp_nn

/-- **Per-`(k, r)` regime-split bound**: for any `(k ≥ 1, r ≥ 0, τ > 0)`, the
per-`(k, r)` bad-event measure is bounded by *either* the M=2 explicit bound
*or* the linear explicit bound — whichever is tighter. Concretely, since
both bounds hold simultaneously, their pointwise minimum also bounds the
measure. This is the "best of both regimes" form: tight in the short regime
(M=2 ≪ linear) and tight in the long regime (linear ≪ M=2). -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_regime_split (k r : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal (min
      ((8 * Real.pi * (k : ℝ) / τ + 4) *
        (4 * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r))))
      ((8 * Real.pi * (k : ℝ) / τ + 4) *
        (4 * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
          (64 * Real.pi^2 * (k : ℝ)^2))))) := by
  -- Both bounds individually apply, so the min applies.
  have h_M2 := apssv_per_kr_measure_le_M2_explicit k r hk τ hτ
  have h_lin := apssv_per_kr_measure_le_linear_explicit k r hk τ hτ
  rw [ENNReal.ofReal_min]
  exact le_min h_M2 h_lin

/-- **Threshold positivity**: for `C > 0` and `k ≥ 1`, the per-`(k, r)` bound
threshold `τ(C, k, r) := C · √(r + b(k)) · min(2^{r/2}, 2^{b(k) - r/2})` is
strictly positive. Used as a precondition for the per-(k, r) sub-Gaussian
helpers (`apssv_per_kr_measure_le_M2_explicit`,
`apssv_per_kr_measure_le_linear_explicit`, `apssv_per_kr_measure_le_regime_split`)
when chaining through the summation argument.

For `k = 1`: `b(1) = 2`, so `r + b ≥ 2 > 0`, hence `√(r+b) > 0`. The `min`
factor is positive (both arguments are positive powers of `2`). With `C > 0`,
the product is positive. -/
@[category API, AMS 11]
lemma apssv_threshold_pos (C : ℝ) (hC : 0 < C) (k r : ℕ) (_hk : 1 ≤ k) :
    0 < C * Real.sqrt ((r : ℝ) + apssvB k) *
      min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) := by
  -- apssvB k ≥ 2 for k ≥ 1, so r + b ≥ 2.
  have h_b_pos : 0 < apssvB k := by
    unfold apssvB
    omega
  have h_b_ge_one : (1 : ℝ) ≤ (apssvB k : ℝ) := by
    have : 1 ≤ apssvB k := h_b_pos
    exact_mod_cast this
  have h_sum_pos : 0 < (r : ℝ) + (apssvB k : ℝ) := by
    have h_r_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    linarith
  have h_sqrt_pos : 0 < Real.sqrt ((r : ℝ) + apssvB k) := Real.sqrt_pos.mpr h_sum_pos
  have h_2pow_r_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h_2pow_b_pos : (0 : ℝ) < (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h_min_pos : 0 < min ((2 : ℝ) ^ ((r : ℝ) / 2))
      ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) :=
    lt_min h_2pow_r_pos h_2pow_b_pos
  positivity

/- ## Auxiliary existential-`h` per-`(k, r)` helpers

The three lemmas below are weaker than `apssv_exists_h_residue_shift_strong`,
which gives an explicit `2^h ≤ 8π·k/τ + 4` upper bound. They expose the cleaner
`(τ/2)²` exp form but with `h` as an existential, leaving the prefactor `2^h`
as a symbolic witness rather than a polynomial-in-`(k, 1/τ)` quantity. They
document the intermediate structural step from an existential residue depth to
the explicit prefactor used in the regime-split bounds. -/

/-- Existential residue-depth version of `apssv_exists_h_residue_shift_strong`.
For `(k, τ)` with `τ > 0`, there exists `h : ℕ` such that `2π·k/2^h ≤ τ/2`,
hence `τ - 2π·k/2^h ≥ τ/2 > 0`. Strengthening of `apssv_exists_h_residue_shift`
without the explicit `2^h` bound — `_strong` provides both. -/
@[category API, AMS 11]
lemma apssv_exists_h_residue_shift_half (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ h : ℕ, τ / 2 ≤ τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by
  have hτ_half : 0 < τ / 2 := by linarith
  obtain ⟨h, h_lt⟩ := apssv_exists_h_residue_shift k (τ / 2) hτ_half
  -- h_lt : 0 < τ/2 - 2π·k/2^h, i.e., 2π·k/2^h < τ/2.
  exact ⟨h, by linarith⟩

/-- Existential-residue-depth version of `apssv_per_kr_measure_le_M2_explicit`.
Per-`(k, r)` sub-Gaussian bound (M=2) with `τ/2` exp form, exposing the
existential `h`. The `_explicit` variant additionally bounds the prefactor by
`8π·k/τ + 4`, eliminating the existential. -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_M2_half (k r : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ h : ℕ, apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal ((2 : ℝ) ^ h *
      (4 * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r)))) := by
  obtain ⟨h, h_half⟩ := apssv_exists_h_residue_shift_half k τ hτ
  refine ⟨h, ?_⟩
  -- Get the raw M=2 bound first.
  have hτ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by linarith
  have h_M2 := apssv_per_kr_measure_le_M2 k r h hk τ hτ_pos
  -- Upgrade the exp argument from (τ')² to (τ/2)² (a weaker but cleaner form).
  refine h_M2.trans (ENNReal.ofReal_le_ofReal ?_)
  set τ' : ℝ := τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h with hτ'_def
  -- Goal: 2^h · 4·exp(-(τ')²/(16·2^r)) ≤ 2^h · 4·exp(-(τ/2)²/(16·2^r)).
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have h_2pow_r_pos : (0 : ℝ) < 16 * (2 : ℝ) ^ r := by positivity
  have h_τ_half_pos : 0 < τ / 2 := by linarith
  have h_τ_half_sq_le : (τ / 2)^2 ≤ τ'^2 := by
    apply sq_le_sq'
    · linarith
    · exact h_half
  have h_neg_le : -(τ')^2 / (16 * (2 : ℝ)^r) ≤ -(τ / 2)^2 / (16 * (2 : ℝ)^r) :=
    div_le_div_of_nonneg_right (by linarith) h_2pow_r_pos.le
  have h_exp_le : Real.exp (-(τ')^2 / (16 * (2 : ℝ)^r)) ≤
      Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r)) :=
    Real.exp_le_exp.mpr h_neg_le
  have h_4_exp_le : (4 : ℝ) * Real.exp (-(τ')^2 / (16 * (2 : ℝ)^r)) ≤
      4 * Real.exp (-(τ / 2)^2 / (16 * (2 : ℝ)^r)) :=
    mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
  exact mul_le_mul_of_nonneg_left h_4_exp_le h_2pow_pos.le

/-- Existential-residue-depth version of `apssv_per_kr_measure_le_linear_explicit`.
Linear analog of `apssv_per_kr_measure_le_M2_half`. -/
@[category API, AMS 11]
lemma apssv_per_kr_measure_le_linear_half (k r : ℕ) (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ h : ℕ, apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
      τ < ‖apssvBlockSum η P r k‖} ≤
    ENNReal.ofReal ((2 : ℝ) ^ h *
      (4 * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
        (64 * Real.pi^2 * (k : ℝ)^2)))) := by
  obtain ⟨h, h_half⟩ := apssv_exists_h_residue_shift_half k τ hτ
  refine ⟨h, ?_⟩
  have hτ_pos : 0 < τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h := by linarith
  have h_lin := apssv_per_kr_measure_le_linear k r h hk τ hτ_pos
  refine h_lin.trans (ENNReal.ofReal_le_ofReal ?_)
  set τ' : ℝ := τ - 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ h with hτ'_def
  have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_denom_pos : (0 : ℝ) < 64 * Real.pi^2 * (k : ℝ)^2 := by
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    positivity
  have h_τ_half_pos : 0 < τ / 2 := by linarith
  have h_τ_half_sq_le : (τ / 2)^2 ≤ τ'^2 := by
    apply sq_le_sq'
    · linarith
    · exact h_half
  have h_2pow_r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have h_mul_le : (τ / 2)^2 * (2 : ℝ)^r ≤ τ'^2 * (2 : ℝ)^r :=
    mul_le_mul_of_nonneg_right h_τ_half_sq_le h_2pow_r_pos.le
  have h_neg_le : -(τ'^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2) ≤
      -((τ / 2)^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2) :=
    div_le_div_of_nonneg_right (by linarith) h_denom_pos.le
  have h_exp_le : Real.exp (-(τ'^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) ≤
      Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) :=
    Real.exp_le_exp.mpr h_neg_le
  have h_4_exp_le : (4 : ℝ) *
        Real.exp (-(τ'^2 * (2 : ℝ)^r) / (64 * Real.pi^2 * (k : ℝ)^2)) ≤
      4 * Real.exp (-((τ / 2)^2 * (2 : ℝ)^r) /
        (64 * Real.pi^2 * (k : ℝ)^2)) :=
    mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
  exact mul_le_mul_of_nonneg_left h_4_exp_le h_2pow_pos.le

/- ## Real-valued regime-split bound (Tannery setup)

Helpers used to discharge the residual real-arithmetic claim of
`apssv_exists_C_with_bad_event_lt_one` via Tannery's dominated convergence
theorem (`tendsto_tsum_of_dominated_convergence`).  We isolate the closed
form of the regime-split upper bound — i.e. the `min` of M=2 and linear
exponential terms appearing in the goal — as a function of `C` (and
`k, r`), prove the per-`(k, r)` Tendsto-to-zero in `C`, and finally invoke
Tannery to get the double-tsum to-zero, which yields a witness `C` with
the resulting tsum strictly below `1`. -/

/-- The per-`(k, r)` real-valued regime-split bound (the term whose
`ENNReal.ofReal` appears under the inner tsum in the goal of
`apssv_exists_C_with_bad_event_lt_one`).

For `k = 0` *or* `C ≤ 0` we set the bound to `0` (vacuous: the
corresponding event is empty for `k = 0`, and the bound is only used as
a Tannery dominator on `C > 0`).  For `k ≥ 1` and `C > 0`, it is the
`min` of the two explicit M=2 / linear sub-Gaussian envelope values at
threshold `τ := C · √(r + b(k)) · min(2^{r/2}, 2^{b-r/2})`. -/
noncomputable def apssvRegimeSplitBoundReal (C : ℝ) (k r : ℕ) : ℝ :=
  if _h : 1 ≤ k ∧ 0 < C then
    let τ := C * Real.sqrt ((r : ℝ) + apssvB k) *
      min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))
    min
      ((8 * Real.pi * (k : ℝ) / τ + 4) *
        (4 * Real.exp (-(τ / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
      ((8 * Real.pi * (k : ℝ) / τ + 4) *
        (4 * Real.exp (-((τ / 2) ^ 2 * (2 : ℝ) ^ r) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))))
  else 0

/-- The regime-split real bound is nonnegative. -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_nonneg (C : ℝ) (k r : ℕ) :
    0 ≤ apssvRegimeSplitBoundReal C k r := by
  unfold apssvRegimeSplitBoundReal
  by_cases h : 1 ≤ k ∧ 0 < C
  · simp only [dif_pos h]
    obtain ⟨hk, hC⟩ := h
    have hτ_pos : 0 < C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) :=
      apssv_threshold_pos C hC k r hk
    set τ : ℝ := C * Real.sqrt ((r : ℝ) + apssvB k) *
      min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) with hτ_def
    have h_k_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_pre_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / τ + 4 := by
      have h_div_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / τ := by
        apply div_nonneg
        · positivity
        · linarith
      linarith
    have h_exp1_pos : 0 < Real.exp (-(τ / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) :=
      Real.exp_pos _
    have h_exp2_pos : 0 < Real.exp (-((τ / 2) ^ 2 * (2 : ℝ) ^ r) /
        (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) := Real.exp_pos _
    refine le_min ?_ ?_
    · exact mul_nonneg h_pre_nn (by linarith [h_exp1_pos])
    · exact mul_nonneg h_pre_nn (by linarith [h_exp2_pos])
  · rw [dif_neg h]

/-- The per-`(k, r)` regime-split real bound tends to `0` as `C → ∞`.

For `k = 0` the function is constantly `0`.  For `k ≥ 1`, we use the
squeeze theorem with the M=2 envelope as upper bound: as `C → ∞`,
`τ = C·α(k, r)` with `α > 0`, so the prefactor `8π·k/τ + 4` tends to
`4` and the exp factor `exp(-(τ/2)²/(16·2^r)) = exp(-α²/(64·2^r) · C²)`
tends to `0`.

Proof: constants definitions, M2-term Tendsto-to-zero via product
of Tendstos, squeeze with `min ≤ M2` after a let-binder unfold. -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_tendsto_zero (k r : ℕ) :
    Filter.Tendsto (fun C : ℝ => apssvRegimeSplitBoundReal C k r)
      Filter.atTop (nhds (0 : ℝ)) := by
  by_cases hk : 1 ≤ k
  · -- For `k ≥ 1`: squeeze min ≤ M2_term, M2_term → 0.
    -- α := √(r+b) · min(2^{r/2}, 2^{b-r/2}) > 0.
    have h_b_pos : 0 < apssvB k := by unfold apssvB; omega
    have h_b_real_pos : (0 : ℝ) < (apssvB k : ℝ) := by exact_mod_cast h_b_pos
    have h_sum_pos : 0 < (r : ℝ) + (apssvB k : ℝ) := by
      have h_r_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
      linarith
    have h_sqrt_pos : 0 < Real.sqrt ((r : ℝ) + apssvB k) := Real.sqrt_pos.mpr h_sum_pos
    have h_2pow_r_rpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_2pow_b_pos : (0 : ℝ) < (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_min_pos : 0 < min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) :=
      lt_min h_2pow_r_rpow_pos h_2pow_b_pos
    have hα_pos : 0 < Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2))
          ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) :=
      mul_pos h_sqrt_pos h_min_pos
    -- M2_term(C, τ) := (8πk/τ + 4) · (4 · exp(-(τ/2)²/(16·2^r))).
    -- With τ = C * α: M2_term(C, Cα) → 0 as C → ∞.
    set α : ℝ := Real.sqrt ((r : ℝ) + apssvB k) *
      min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) with hα_def
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_2pow_r_pos' : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have h_Cα_atTop : Filter.Tendsto (fun C : ℝ => C * α) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hα_pos
    have h_inv_tendsto : Filter.Tendsto
        (fun C : ℝ => 8 * Real.pi * (k : ℝ) / (C * α))
        Filter.atTop (nhds 0) :=
      h_Cα_atTop.const_div_atTop _
    have h_pre_tendsto : Filter.Tendsto
        (fun C : ℝ => 8 * Real.pi * (k : ℝ) / (C * α) + 4)
        Filter.atTop (nhds (0 + 4)) :=
      h_inv_tendsto.add tendsto_const_nhds
    have h_exp_arg_tendsto : Filter.Tendsto
        (fun C : ℝ => -(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))
        Filter.atTop Filter.atBot := by
      have h_coeff_neg : -(α ^ 2 / (64 * (2 : ℝ) ^ r)) < 0 := by
        have : 0 < α ^ 2 / (64 * (2 : ℝ) ^ r) := by positivity
        linarith
      have key : Filter.Tendsto
          (fun C : ℝ => -(α ^ 2 / (64 * (2 : ℝ) ^ r)) * C ^ 2)
          Filter.atTop Filter.atBot :=
        tendsto_neg_const_mul_pow_atTop (by norm_num) h_coeff_neg
      apply key.congr'
      filter_upwards with C
      ring
    have h_exp_tendsto : Filter.Tendsto
        (fun C : ℝ => Real.exp (-(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)))
        Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_exp_arg_tendsto
    have h_4exp_tendsto : Filter.Tendsto
        (fun C : ℝ => 4 * Real.exp (-(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)))
        Filter.atTop (nhds (4 * 0)) :=
      tendsto_const_nhds.mul h_exp_tendsto
    have h_M2_tendsto : Filter.Tendsto
        (fun C : ℝ => (8 * Real.pi * (k : ℝ) / (C * α) + 4) *
          (4 * Real.exp (-(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
        Filter.atTop (nhds ((0 + 4) * (4 * 0))) :=
      h_pre_tendsto.mul h_4exp_tendsto
    have h_M2_tendsto_zero : Filter.Tendsto
        (fun C : ℝ => (8 * Real.pi * (k : ℝ) / (C * α) + 4) *
          (4 * Real.exp (-(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
        Filter.atTop (nhds 0) := by simpa using h_M2_tendsto
    -- Squeeze: 0 ≤ apssvRegimeSplitBoundReal C k r ≤ M2_term(C) (for C > 0
    -- the bound equals min(M2, lin) ≤ M2; for C ≤ 0 the bound = 0 ≤ M2_term
    -- which may be negative — so we use the eventually-squeeze).
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ))) h_M2_tendsto_zero ?_ ?_
    · filter_upwards with C
      exact apssvRegimeSplitBoundReal_nonneg C k r
    · -- For C > 0: apssvRegimeSplitBoundReal C k r = min(M2, lin) ≤ M2.
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with C hC_pos
      -- Use the explicit form via the regime_split helper.  The cleanest
      -- way is to compute via the `_explicit` helper match.
      have h_unfold : apssvRegimeSplitBoundReal C k r =
          min
            ((8 * Real.pi * (k : ℝ) / (C * α) + 4) *
              (4 * Real.exp (-(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
            ((8 * Real.pi * (k : ℝ) / (C * α) + 4) *
              (4 * Real.exp (-((C * α / 2) ^ 2 * (2 : ℝ) ^ r) /
                (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)))) := by
        unfold apssvRegimeSplitBoundReal
        rw [dif_pos ⟨hk, hC_pos⟩]
        -- After dif_pos, the body is `let τ := ...; min A(τ) B(τ)`.
        -- We want this = `min A(C*α) B(C*α)`.  Reduce the let:
        show
          (let τ := C * Real.sqrt ((r : ℝ) + apssvB k) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))
          min
            ((8 * Real.pi * (k : ℝ) / τ + 4) *
              (4 * Real.exp (-(τ / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
            ((8 * Real.pi * (k : ℝ) / τ + 4) *
              (4 * Real.exp (-((τ / 2) ^ 2 * (2 : ℝ) ^ r) /
                (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))))) = _
        have h_τ_eq : C * Real.sqrt ((r : ℝ) + apssvB k) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) = C * α := by
          rw [hα_def]; ring
        rw [h_τ_eq]
      rw [h_unfold]
      exact min_le_left _ _
  · -- For k = 0: constantly 0.
    have h_const : (fun C : ℝ => apssvRegimeSplitBoundReal C k r) = fun _ => (0 : ℝ) := by
      funext C
      unfold apssvRegimeSplitBoundReal
      have h_neg : ¬ (1 ≤ k ∧ 0 < C) := fun ⟨h, _⟩ => hk h
      rw [dif_neg h_neg]
    rw [h_const]
    exact tendsto_const_nhds

/-- The per-`(k, r)` regime-split real bound is *antitone* in `C` on the
positive reals.

For `k = 0` *or* `C ≤ 0` the bound is `0` (constant). For `k ≥ 1` and
`0 < C₁ ≤ C₂`, write `τ(C) = C · α(k, r)` with `α(k, r) > 0` (independent
of `C`). Then
* `8π·k/τ(C) + 4` is decreasing in `C` (positive function with denominator
  increasing in `C`);
* `(τ(C)/2)² = C²·α²/4` is increasing in `C`, so each `exp(-(τ/2)²/...)`
  factor is decreasing in `C`;
* both factors are positive, so each *product* is decreasing;
* the `min` of two antitone functions is antitone. -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_antitone_on_pos (k r : ℕ) :
    AntitoneOn (fun C => apssvRegimeSplitBoundReal C k r) (Set.Ioi 0) := by
  intro C₁ hC₁ C₂ hC₂ h_le
  -- hC₁, hC₂ : 0 < C₁, 0 < C₂; h_le : C₁ ≤ C₂.
  rw [Set.mem_Ioi] at hC₁ hC₂
  by_cases hk : 1 ≤ k
  · -- k ≥ 1 case: both τ are positive; explicit comparison.
    -- Set up α := √(r+b)·min(2^{r/2}, 2^{b-r/2}) > 0.
    have h_b_pos : 0 < apssvB k := by unfold apssvB; omega
    have h_b_real_pos : (0 : ℝ) < (apssvB k : ℝ) := by exact_mod_cast h_b_pos
    have h_sum_pos : 0 < (r : ℝ) + (apssvB k : ℝ) := by
      have h_r_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
      linarith
    have h_sqrt_pos : 0 < Real.sqrt ((r : ℝ) + apssvB k) := Real.sqrt_pos.mpr h_sum_pos
    have h_2pow_r_rpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_2pow_b_pos : (0 : ℝ) < (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_min_pos : 0 < min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) :=
      lt_min h_2pow_r_rpow_pos h_2pow_b_pos
    set α : ℝ := Real.sqrt ((r : ℝ) + apssvB k) *
      min ((2 : ℝ) ^ ((r : ℝ) / 2))
        ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) with hα_def
    have hα_pos : 0 < α := mul_pos h_sqrt_pos h_min_pos
    -- Unfold both sides into the dif_pos branch.
    have h_unfold : ∀ C, 0 < C → apssvRegimeSplitBoundReal C k r =
        min
          ((8 * Real.pi * (k : ℝ) / (C * α) + 4) *
            (4 * Real.exp (-(C * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
          ((8 * Real.pi * (k : ℝ) / (C * α) + 4) *
            (4 * Real.exp (-((C * α / 2) ^ 2 * (2 : ℝ) ^ r) /
              (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)))) := by
      intro C hC_pos
      unfold apssvRegimeSplitBoundReal
      rw [dif_pos ⟨hk, hC_pos⟩]
      show
        (let τ := C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2))
            ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))
        min
          ((8 * Real.pi * (k : ℝ) / τ + 4) *
            (4 * Real.exp (-(τ / 2) ^ 2 / (16 * (2 : ℝ) ^ r))))
          ((8 * Real.pi * (k : ℝ) / τ + 4) *
            (4 * Real.exp (-((τ / 2) ^ 2 * (2 : ℝ) ^ r) /
              (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))))) = _
      have h_τ_eq : C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2))
            ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) = C * α := by
        rw [hα_def]; ring
      rw [h_τ_eq]
    show apssvRegimeSplitBoundReal C₂ k r ≤ apssvRegimeSplitBoundReal C₁ k r
    rw [h_unfold C₁ hC₁, h_unfold C₂ hC₂]
    -- Compare the two `min`s termwise.
    have h_C₁α_pos : 0 < C₁ * α := mul_pos hC₁ hα_pos
    have h_C₂α_pos : 0 < C₂ * α := mul_pos hC₂ hα_pos
    have h_C₁α_le_C₂α : C₁ * α ≤ C₂ * α := mul_le_mul_of_nonneg_right h_le hα_pos.le
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h_2pow_r_pos' : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have h_pre_le : 8 * Real.pi * (k : ℝ) / (C₂ * α) + 4 ≤
        8 * Real.pi * (k : ℝ) / (C₁ * α) + 4 := by
      have h_num_nn : 0 ≤ 8 * Real.pi * (k : ℝ) := by positivity
      have h_div_le :
          8 * Real.pi * (k : ℝ) / (C₂ * α) ≤ 8 * Real.pi * (k : ℝ) / (C₁ * α) :=
        div_le_div_of_nonneg_left h_num_nn h_C₁α_pos h_C₁α_le_C₂α
      linarith
    have h_pre_C₂_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / (C₂ * α) + 4 := by
      have h_div_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / (C₂ * α) :=
        div_nonneg (by positivity) h_C₂α_pos.le
      linarith
    -- Compare exp factors: square is increasing in C·α, denom positive,
    -- so -(τ/2)²/denom is decreasing in C.
    have h_sq_le : (C₁ * α / 2) ^ 2 ≤ (C₂ * α / 2) ^ 2 := by
      apply sq_le_sq'
      · nlinarith [h_C₁α_pos, h_C₂α_pos, h_le]
      · linarith
    have h_denom1_pos : (0 : ℝ) < 16 * (2 : ℝ) ^ r := by positivity
    have h_denom2_pos : (0 : ℝ) < 64 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
    have h_neg_sq_le1 :
        -(C₂ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r) ≤
          -(C₁ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r) :=
      div_le_div_of_nonneg_right (by linarith) h_denom1_pos.le
    have h_exp1_le :
        Real.exp (-(C₂ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) ≤
          Real.exp (-(C₁ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) :=
      Real.exp_le_exp.mpr h_neg_sq_le1
    have h_4exp1_le :
        4 * Real.exp (-(C₂ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) ≤
          4 * Real.exp (-(C₁ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) :=
      mul_le_mul_of_nonneg_left h_exp1_le (by norm_num)
    have h_4exp1_C₂_nn : 0 ≤ 4 * Real.exp (-(C₂ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) := by
      have h_exp_pos : 0 < Real.exp (-(C₂ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) :=
        Real.exp_pos _
      linarith
    have h_M2_le :
        (8 * Real.pi * (k : ℝ) / (C₂ * α) + 4) *
          (4 * Real.exp (-(C₂ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))) ≤
        (8 * Real.pi * (k : ℝ) / (C₁ * α) + 4) *
          (4 * Real.exp (-(C₁ * α / 2) ^ 2 / (16 * (2 : ℝ) ^ r))) :=
      mul_le_mul h_pre_le h_4exp1_le h_4exp1_C₂_nn
        (by linarith [h_pre_le, h_pre_C₂_nn])
    -- Linear-term comparison.
    have h_sq_2pow_le : (C₁ * α / 2) ^ 2 * (2 : ℝ) ^ r ≤
        (C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right h_sq_le h_2pow_r_pos'.le
    have h_neg_sq_le2 :
        -((C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r) / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2) ≤
          -((C₁ * α / 2) ^ 2 * (2 : ℝ) ^ r) / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) h_denom2_pos.le
    have h_exp2_le :
        Real.exp (-((C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) ≤
        Real.exp (-((C₁ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) :=
      Real.exp_le_exp.mpr h_neg_sq_le2
    have h_4exp2_le :
        4 * Real.exp (-((C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) ≤
        4 * Real.exp (-((C₁ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left h_exp2_le (by norm_num)
    have h_4exp2_C₂_nn : 0 ≤ 4 * Real.exp (-((C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
        (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) := by
      have h_exp_pos : 0 < Real.exp (-((C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) := Real.exp_pos _
      linarith
    have h_lin_le :
        (8 * Real.pi * (k : ℝ) / (C₂ * α) + 4) *
          (4 * Real.exp (-((C₂ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
            (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))) ≤
        (8 * Real.pi * (k : ℝ) / (C₁ * α) + 4) *
          (4 * Real.exp (-((C₁ * α / 2) ^ 2 * (2 : ℝ) ^ r) /
            (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))) :=
      mul_le_mul h_pre_le h_4exp2_le h_4exp2_C₂_nn
        (by linarith [h_pre_le, h_pre_C₂_nn])
    exact min_le_min h_M2_le h_lin_le
  · -- k = 0 case: both sides equal 0.
    have h_neg₁ : ¬ (1 ≤ k ∧ 0 < C₁) := fun ⟨h, _⟩ => hk h
    have h_neg₂ : ¬ (1 ≤ k ∧ 0 < C₂) := fun ⟨h, _⟩ => hk h
    show apssvRegimeSplitBoundReal C₂ k r ≤ apssvRegimeSplitBoundReal C₁ k r
    unfold apssvRegimeSplitBoundReal
    rw [dif_neg h_neg₂, dif_neg h_neg₁]

/-- Real-valued tsum-tendsto-zero (Tannery's): given a summability witness
at some `C₀ > 0`, the (real-valued) double tsum tends to `0` as `C → ∞`.

This uses the antitone-in-`C` lemma `apssvRegimeSplitBoundReal_antitone_on_pos`
to dominate the integrand for `C ≥ C₀`, and the per-term tendsto-zero lemma
`apssvRegimeSplitBoundReal_tendsto_zero`. The summability hypothesis is the
*irreducible* heavy step (geometric series in `(k, r)`). -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_real_tsum_tendsto_zero
    (h_summable : ∃ C₀ > 0, Summable
      (fun kr : ℕ × ℕ => apssvRegimeSplitBoundReal C₀ kr.1 kr.2)) :
    Filter.Tendsto (fun C : ℝ =>
        ∑' kr : ℕ × ℕ, apssvRegimeSplitBoundReal C kr.1 kr.2)
      Filter.atTop (nhds 0) := by
  obtain ⟨C₀, hC₀_pos, h_sum⟩ := h_summable
  -- Apply Tannery: f(C, kr) → 0, dominated by bound(kr) := f(C₀, kr).
  have h_tannery := tendsto_tsum_of_dominated_convergence
    (𝓕 := Filter.atTop) (α := ℝ) (β := ℕ × ℕ) (G := ℝ)
    (f := fun C kr => apssvRegimeSplitBoundReal C kr.1 kr.2)
    (g := fun _ => (0 : ℝ))
    (bound := fun kr => apssvRegimeSplitBoundReal C₀ kr.1 kr.2)
    h_sum
    (fun kr => apssvRegimeSplitBoundReal_tendsto_zero kr.1 kr.2)
    (by
      filter_upwards [Filter.eventually_ge_atTop C₀,
        Filter.eventually_gt_atTop (0 : ℝ)] with C hC h_pos kr
      have h_anti :=
        apssvRegimeSplitBoundReal_antitone_on_pos kr.1 kr.2
          (Set.mem_Ioi.mpr hC₀_pos) (Set.mem_Ioi.mpr h_pos) hC
      have h_nn := apssvRegimeSplitBoundReal_nonneg C kr.1 kr.2
      simpa [Real.norm_eq_abs, abs_of_nonneg h_nn] using h_anti)
  -- The target tsum is `∑' kr, 0 = 0`.
  simpa [tsum_zero] using h_tannery

/-- ENNReal version of the tsum-tendsto-zero (the form actually needed by the
main lemma): `∑' k, ∑' r, ENNReal.ofReal (...) → 0` as `C → ∞`. -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_ennreal_tsum_tendsto_zero
    (h_summable : ∃ C₀ > 0, Summable
      (fun kr : ℕ × ℕ => apssvRegimeSplitBoundReal C₀ kr.1 kr.2)) :
    Filter.Tendsto (fun C : ℝ =>
        ∑' k : ℕ, ∑' r : ℕ, ENNReal.ofReal (apssvRegimeSplitBoundReal C k r))
      Filter.atTop (nhds 0) := by
  obtain ⟨C₀, hC₀_pos, h_sum⟩ := h_summable
  -- Real-valued tendsto: ∑' kr, real bound → 0.
  have h_real_tendsto :
      Filter.Tendsto (fun C : ℝ =>
          ∑' kr : ℕ × ℕ, apssvRegimeSplitBoundReal C kr.1 kr.2)
        Filter.atTop (nhds 0) :=
    apssvRegimeSplitBoundReal_real_tsum_tendsto_zero ⟨C₀, hC₀_pos, h_sum⟩
  -- Lift to ENNReal.ofReal: continuous, and ofReal 0 = 0.
  have h_ennreal_real_tendsto :
      Filter.Tendsto (fun C : ℝ =>
          ENNReal.ofReal (∑' kr : ℕ × ℕ, apssvRegimeSplitBoundReal C kr.1 kr.2))
        Filter.atTop (nhds (ENNReal.ofReal 0)) :=
    ENNReal.tendsto_ofReal h_real_tendsto
  rw [ENNReal.ofReal_zero] at h_ennreal_real_tendsto
  -- For C ≥ C₀ (eventually), the real-valued sum equals
  --   ∑' kr, ENNReal.ofReal (real bound)
  -- via `ENNReal.ofReal_tsum_of_nonneg` (using nonneg + summability via
  -- antitone domination). Then `ENNReal.tsum_prod` swaps to the iterated
  -- form `∑' k, ∑' r, ...`.
  apply h_ennreal_real_tendsto.congr'
  filter_upwards [Filter.eventually_ge_atTop C₀,
    Filter.eventually_gt_atTop (0 : ℝ)] with C hC hC_pos
  -- Domination by C₀-bound gives summability at C.
  have h_anti_C :
      ∀ kr : ℕ × ℕ, apssvRegimeSplitBoundReal C kr.1 kr.2 ≤
        apssvRegimeSplitBoundReal C₀ kr.1 kr.2 := by
    intro kr
    exact apssvRegimeSplitBoundReal_antitone_on_pos kr.1 kr.2
      (Set.mem_Ioi.mpr hC₀_pos) (Set.mem_Ioi.mpr hC_pos) hC
  have h_nn_C : ∀ kr : ℕ × ℕ, 0 ≤ apssvRegimeSplitBoundReal C kr.1 kr.2 :=
    fun kr => apssvRegimeSplitBoundReal_nonneg C kr.1 kr.2
  have h_sum_C : Summable
      (fun kr : ℕ × ℕ => apssvRegimeSplitBoundReal C kr.1 kr.2) :=
    h_sum.of_nonneg_of_le h_nn_C h_anti_C
  -- Step 1: ENNReal.ofReal of real tsum = tsum of ENNReal.ofReal.
  rw [ENNReal.ofReal_tsum_of_nonneg h_nn_C h_sum_C]
  -- Step 2: `ENNReal.tsum_prod` converts `∑' kr` to `∑' k, ∑' r`.
  exact ENNReal.tsum_prod
    (f := fun k r => ENNReal.ofReal (apssvRegimeSplitBoundReal C k r))

/- ### Envelope decomposition for summability

We dominate `apssvRegimeSplitBoundReal C k r` by a sum of two
"regime-restricted" envelopes — `apssvShortEnvelope` (active when
`r ≤ apssvB k`, dominates the `M=2` arm) and `apssvLongEnvelope` (active
when `apssvB k < r`, dominates the `linear` arm). Each envelope is
explicitly geometrically summable in `(k, r) ∈ ℕ × ℕ` for `C` large.

The envelopes use:
* In `apssvShortEnvelope`: prefactor `(8π·2^b/C + 4)·4`, exp argument
  `-C²·(r + b)/64`. Replaces `8πk/τ` with `8π·2^b/C` (using `2k ≤ 2^b`).
* In `apssvLongEnvelope`: prefactor `(8π·2^{r/2}/C + 4)·4`, exp argument
  `-C²·(r + b)/(64π²)`. Replaces `8πk/τ` with `8π·2^{r/2}/C`.

The pointwise bound `apssvRegimeSplitBoundReal C k r ≤ shortEnv + longEnv`
holds for all `k, r` (with `k ≥ 1, C > 0`), with the regime split
ensuring that in each regime, exactly one envelope dominates the active arm
of the `min`. -/

/-- `2 * k < 2 ^ apssvB k`, i.e., the dyadic-cap bound `2k < 2^b`. Standard
property of `Nat.log2`. Trivially true for `k = 0` (`0 < 2^1`); for `k ≥ 1`
it follows from `Nat.lt_pow_succ_log_self`. -/
@[category API, AMS 11]
lemma apssv_two_k_lt_two_pow_b (k : ℕ) :
    2 * k < 2 ^ apssvB k := by
  unfold apssvB
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * k)

/-- Real-cast version: `(2k : ℝ) ≤ 2^(apssvB k)`. -/
@[category API, AMS 11]
lemma apssv_two_k_le_two_pow_b_real (k : ℕ) :
    (2 * k : ℝ) ≤ (2 : ℝ) ^ apssvB k := by
  have h := apssv_two_k_lt_two_pow_b k
  have : ((2 * k : ℕ) : ℝ) ≤ ((2 ^ apssvB k : ℕ) : ℝ) := by exact_mod_cast h.le
  push_cast at this
  exact this

/-- Short-regime envelope: `(8π·2^b/C + 4)·4·exp(-C²·(r+b)/64)` for `k ≥ 1, C > 0`,
otherwise `0`. Dominates `apssvRegimeSplitBoundReal` in the regime `r ≤ apssvB k`.
-/
noncomputable def apssvShortEnvelope (C : ℝ) (k r : ℕ) : ℝ :=
  if 1 ≤ k ∧ 0 < C then
    (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C + 4) * 4 *
      Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64)
  else 0

/-- Long-regime envelope: `(8π·2^(r/2)/C + 4)·4·exp(-C²·(r+b)/(64π²))` for
`k ≥ 1, C > 0`, otherwise `0`. Dominates `apssvRegimeSplitBoundReal` in the
regime `apssvB k < r`. -/
noncomputable def apssvLongEnvelope (C : ℝ) (k r : ℕ) : ℝ :=
  if 1 ≤ k ∧ 0 < C then
    (8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / C + 4) * 4 *
      Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2))
  else 0

/-- The short envelope is non-negative. -/
@[category API, AMS 11]
lemma apssvShortEnvelope_nonneg (C : ℝ) (k r : ℕ) :
    0 ≤ apssvShortEnvelope C k r := by
  unfold apssvShortEnvelope
  split_ifs with h
  · obtain ⟨_, hC⟩ := h
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (apssvB k) := by positivity
    have h_pre_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C + 4 := by
      have h_div_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C :=
        div_nonneg (by positivity) hC.le
      linarith
    have h_exp_nn : 0 ≤ Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64) :=
      (Real.exp_pos _).le
    positivity
  · exact le_refl _

/-- The long envelope is non-negative. -/
@[category API, AMS 11]
lemma apssvLongEnvelope_nonneg (C : ℝ) (k r : ℕ) :
    0 ≤ apssvLongEnvelope C k r := by
  unfold apssvLongEnvelope
  split_ifs with h
  · obtain ⟨_, hC⟩ := h
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_pre_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / C + 4 := by
      have h_div_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / C :=
        div_nonneg (by positivity) hC.le
      linarith
    have h_exp_nn : 0 ≤ Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) :=
      (Real.exp_pos _).le
    positivity
  · exact le_refl _

/-- In the short regime `r ≤ apssvB k`, the M=2 arm is dominated by the
short envelope: `M2_term ≤ apssvShortEnvelope`.

The proof uses `min(2^(r/2), 2^(b-r/2)) = 2^(r/2)` (since `r ≤ b`) to
simplify `τ`, then bounds `8πk/τ ≤ 8π·2^b/C` via `2k ≤ 2^b`,
`√(r+b) ≥ 1`, `2^(r/2) ≥ 1`. The exp argument simplifies exactly to
`-C²(r+b)/64`. -/
@[category API, AMS 11]
lemma apssv_M2_term_le_short_envelope (C : ℝ) (hC : 0 < C) (k r : ℕ)
    (hk : 1 ≤ k) (hr : r ≤ apssvB k) :
    (8 * Real.pi * (k : ℝ) / (C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
      (4 * Real.exp (-(C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 /
          (16 * (2 : ℝ) ^ r))) ≤
      apssvShortEnvelope C k r := by
  -- Simplify τ in short regime: min = 2^(r/2).
  have h_b_pos : 0 < apssvB k := by unfold apssvB; omega
  have h_b_real_pos : (0 : ℝ) < (apssvB k : ℝ) := by exact_mod_cast h_b_pos
  have h_b_ge_one : (1 : ℝ) ≤ (apssvB k : ℝ) := by exact_mod_cast h_b_pos
  have h_r_real_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have h_r_le_b_real : (r : ℝ) ≤ (apssvB k : ℝ) := by exact_mod_cast hr
  have h_sum_pos : 0 < (r : ℝ) + (apssvB k : ℝ) := by linarith
  have h_sum_ge_one : 1 ≤ (r : ℝ) + (apssvB k : ℝ) := by linarith
  have h_sqrt_pos : 0 < Real.sqrt ((r : ℝ) + apssvB k) := Real.sqrt_pos.mpr h_sum_pos
  have h_sqrt_ge_one : 1 ≤ Real.sqrt ((r : ℝ) + apssvB k) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt h_sum_ge_one
  have h_2pow_r_rpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h_2pow_b_pos : (0 : ℝ) < (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- min = 2^(r/2): r ≤ b ⟹ r/2 ≤ b - r/2 ⟹ 2^(r/2) ≤ 2^(b-r/2).
  have h_r_half_le : (r : ℝ) / 2 ≤ (apssvB k : ℝ) - (r : ℝ) / 2 := by linarith
  have h_2pow_le : (2 : ℝ) ^ ((r : ℝ) / 2) ≤ (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h_r_half_le
  have h_min_eq : min ((2 : ℝ) ^ ((r : ℝ) / 2))
      ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) = (2 : ℝ) ^ ((r : ℝ) / 2) :=
    min_eq_left h_2pow_le
  rw [h_min_eq]
  -- 2^(r/2) ≥ 1.
  have h_2pow_r_half_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ ((r : ℝ) / 2) := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by rw [Real.rpow_zero]]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- 2^r = (2^(r/2))^2 = ((2 : ℝ)^(r : ℝ))^? — actually 2^r as nat-pow.
  have h_2pow_r_nat_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  -- Equation: 2^r = (2^(r/2))^2 (real rpow vs nat pow).
  have h_2pow_r_eq : (2 : ℝ) ^ r = ((2 : ℝ) ^ ((r : ℝ) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) r]
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  -- Set τ_short := C * √(r+b) * 2^(r/2) (the post-min value of τ).
  set sqrtRb := Real.sqrt ((r : ℝ) + apssvB k) with h_sqrt_def
  set p := (2 : ℝ) ^ ((r : ℝ) / 2) with h_p_def
  -- Goal LHS uses τ = C * sqrtRb * p.
  -- Compute (τ/2)² / (16 · 2^r) = C²(r+b)/64.
  have h_sqrt_sq : sqrtRb ^ 2 = (r : ℝ) + apssvB k := by
    rw [h_sqrt_def]; exact Real.sq_sqrt h_sum_pos.le
  have h_p_sq : p ^ 2 = (2 : ℝ) ^ r := by rw [h_p_def, ← h_2pow_r_eq]
  have h_2pow_r_pos' : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have h_tau_sq_eq : (C * sqrtRb * p / 2) ^ 2 / (16 * (2 : ℝ) ^ r)
      = C ^ 2 * ((r : ℝ) + apssvB k) / 64 := by
    have h_num : (C * sqrtRb * p / 2) ^ 2 = C ^ 2 * sqrtRb ^ 2 * p ^ 2 / 4 := by ring
    rw [h_num, h_sqrt_sq, h_p_sq]
    field_simp
    ring
  -- The exp factor in goal becomes exp(-C²(r+b)/64).
  have h_exp_eq : Real.exp (-(C * sqrtRb * p / 2) ^ 2 / (16 * (2 : ℝ) ^ r))
      = Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64) := by
    congr 1
    have h_step : -(C * sqrtRb * p / 2) ^ 2 / (16 * (2 : ℝ) ^ r) =
        -((C * sqrtRb * p / 2) ^ 2 / (16 * (2 : ℝ) ^ r)) := by
      ring
    rw [h_step, h_tau_sq_eq]
    ring
  -- Now bound 8πk/(C·√·p) by 8π·2^b/C.
  -- Need: k/(C·√·p) ≤ 2^b/C ⟺ k ≤ 2^b · √·p (with all positive).
  have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_2pow_b_pow : (0 : ℝ) < (2 : ℝ) ^ (apssvB k) := by positivity
  have h_τ_pos : 0 < C * sqrtRb * p := by
    rw [h_p_def, h_sqrt_def]
    positivity
  have h_2k_le_2pow_b : (2 * k : ℝ) ≤ (2 : ℝ) ^ (apssvB k) :=
    apssv_two_k_le_two_pow_b_real k
  have h_k_le_2pow_b : (k : ℝ) ≤ (2 : ℝ) ^ (apssvB k) := by linarith
  have h_pre_le : 8 * Real.pi * (k : ℝ) / (C * sqrtRb * p) ≤
      8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C := by
    rw [div_le_div_iff₀ h_τ_pos hC]
    -- Goal: 8π·k·C ≤ 8π·2^b · (C·√·p)
    have h_sqp_ge : 1 ≤ sqrtRb * p :=
      one_le_mul_of_one_le_of_one_le h_sqrt_ge_one h_2pow_r_half_ge_one
    have h_pi_nn : 0 ≤ 8 * Real.pi := by have := Real.pi_pos; linarith
    have h_C_nn : 0 ≤ C := hC.le
    -- 8π·k·C ≤ 8π·2^b·C ≤ 8π·2^b·(C·√·p)
    have h1 : 8 * Real.pi * (k : ℝ) * C ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C := by
      have : 8 * Real.pi * (k : ℝ) ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) :=
        mul_le_mul_of_nonneg_left h_k_le_2pow_b h_pi_nn
      exact mul_le_mul_of_nonneg_right this h_C_nn
    have h2 : 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C ≤
        8 * Real.pi * (2 : ℝ) ^ (apssvB k) * (C * sqrtRb * p) := by
      have h_lhs_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) := by positivity
      rw [show 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * (C * sqrtRb * p) =
          8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C * (sqrtRb * p) by ring]
      have h_target_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C := by
        positivity
      calc 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C
          = 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C * 1 := by ring
        _ ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) * C * (sqrtRb * p) :=
            mul_le_mul_of_nonneg_left h_sqp_ge h_target_nn
    linarith
  have h_pre_add_le : 8 * Real.pi * (k : ℝ) / (C * sqrtRb * p) + 4 ≤
      8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C + 4 := by linarith
  -- exp factor is positive (= shortEnv exp factor); 4 * exp ≥ 0.
  have h_exp_pos : 0 < Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64) := Real.exp_pos _
  have h_4exp_nn : 0 ≤ 4 * Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64) := by linarith
  -- Combine.
  have h_pre_C_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / (C * sqrtRb * p) + 4 := by
    have h_div_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / (C * sqrtRb * p) := by
      apply div_nonneg
      · have := Real.pi_pos; positivity
      · exact h_τ_pos.le
    linarith
  unfold apssvShortEnvelope
  rw [if_pos ⟨hk, hC⟩]
  rw [h_exp_eq]
  -- Goal: (8πk/τ + 4) * (4·exp E) ≤ (8π·2^b/C + 4) * 4 * exp E
  rw [show (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C + 4) * 4 *
        Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64) =
        (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / C + 4) *
        (4 * Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / 64)) by ring]
  exact mul_le_mul h_pre_add_le le_rfl h_4exp_nn (by linarith)

/-- In the long regime `apssvB k < r`, the linear arm is dominated by the
long envelope: `lin_term ≤ apssvLongEnvelope`. -/
@[category API, AMS 11]
lemma apssv_linear_term_le_long_envelope (C : ℝ) (hC : 0 < C) (k r : ℕ)
    (hk : 1 ≤ k) (hr : apssvB k < r) :
    (8 * Real.pi * (k : ℝ) / (C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
      (4 * Real.exp (-((C * Real.sqrt ((r : ℝ) + apssvB k) *
        min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 *
        (2 : ℝ) ^ r) / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))) ≤
      apssvLongEnvelope C k r := by
  -- In the long regime, min = 2^(b - r/2).
  have h_b_pos : 0 < apssvB k := by unfold apssvB; omega
  have h_b_real_pos : (0 : ℝ) < (apssvB k : ℝ) := by exact_mod_cast h_b_pos
  have h_b_ge_one : (1 : ℝ) ≤ (apssvB k : ℝ) := by exact_mod_cast h_b_pos
  have h_r_real_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have h_b_le_r_real : (apssvB k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.le
  have h_sum_pos : 0 < (r : ℝ) + (apssvB k : ℝ) := by linarith
  have h_sum_ge_one : 1 ≤ (r : ℝ) + (apssvB k : ℝ) := by linarith
  have h_sqrt_pos : 0 < Real.sqrt ((r : ℝ) + apssvB k) := Real.sqrt_pos.mpr h_sum_pos
  have h_sqrt_ge_one : 1 ≤ Real.sqrt ((r : ℝ) + apssvB k) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt h_sum_ge_one
  have h_2pow_r_rpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h_2pow_b_minus_pos : (0 : ℝ) < (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- min = 2^(b - r/2): b ≤ r ⟹ b - r/2 ≤ r/2.
  have h_b_minus_le : (apssvB k : ℝ) - (r : ℝ) / 2 ≤ (r : ℝ) / 2 := by linarith
  have h_2pow_le : (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) ≤ (2 : ℝ) ^ ((r : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h_b_minus_le
  have h_min_eq : min ((2 : ℝ) ^ ((r : ℝ) / 2))
      ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) =
      (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) :=
    min_eq_right h_2pow_le
  rw [h_min_eq]
  -- 2^(b-r/2) ≥ 0; 2^(r/2) ≥ 1; 2^b - r/2 might be < 1 (if r > 2b).
  -- Set q := 2^(b - r/2).
  set sqrtRb := Real.sqrt ((r : ℝ) + apssvB k) with h_sqrt_def
  set q := (2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2) with h_q_def
  set p := (2 : ℝ) ^ ((r : ℝ) / 2) with h_p_def
  have h_p_pos : 0 < p := h_2pow_r_rpow_pos
  have h_q_pos : 0 < q := h_2pow_b_minus_pos
  have h_2pow_r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  -- Key identity: q² · 2^r = (2^b)² (since q² · 2^r = 2^(2b - r) · 2^r = 2^(2b)).
  have h_q_sq_eq : q ^ 2 = (2 : ℝ) ^ ((apssvB k : ℝ) * 2 - (r : ℝ)) := by
    rw [h_q_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast; ring
  have h_2pow_r_eq : (2 : ℝ) ^ r = (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
  -- 2^(2b - r) · 2^r = 2^(2b)
  have h_2pow_b_sq_eq : ((2 : ℝ) ^ (apssvB k)) ^ 2 = (2 : ℝ) ^ ((apssvB k : ℝ) * 2) := by
    rw [show ((2 : ℝ) ^ (apssvB k)) ^ 2 = (2 : ℝ) ^ (apssvB k) * (2 : ℝ) ^ (apssvB k) by ring]
    rw [show (2 : ℝ) ^ (apssvB k) = (2 : ℝ) ^ ((apssvB k : ℝ)) from
      (Real.rpow_natCast (2 : ℝ) (apssvB k)).symm]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have h_q_sq_2pow_r : q ^ 2 * (2 : ℝ) ^ r = ((2 : ℝ) ^ (apssvB k)) ^ 2 := by
    rw [h_q_sq_eq, h_2pow_r_eq, h_2pow_b_sq_eq]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  -- (τ/2)² · 2^r / (64π²k²) = C²(r+b) · q² · 2^r / (256π²k²)
  -- = C²(r+b) · (2^b)² / (256π²k²) ≥ C²(r+b) / (64π²)  [using (2k)² ≤ (2^b)²]
  have h_τ : 0 < C * sqrtRb * q := by
    rw [h_q_def, h_sqrt_def]
    positivity
  have h_k_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2k_le_2pow_b : (2 * k : ℝ) ≤ (2 : ℝ) ^ (apssvB k) :=
    apssv_two_k_le_two_pow_b_real k
  -- Compute the exp argument exactly.
  have h_sqrt_sq : sqrtRb ^ 2 = (r : ℝ) + apssvB k := by
    rw [h_sqrt_def]; exact Real.sq_sqrt h_sum_pos.le
  have h_τ_sq_2pow_r_eq : (C * sqrtRb * q / 2) ^ 2 * (2 : ℝ) ^ r =
      C ^ 2 * ((r : ℝ) + apssvB k) * ((2 : ℝ) ^ (apssvB k)) ^ 2 / 4 := by
    rw [show (C * sqrtRb * q / 2) ^ 2 * (2 : ℝ) ^ r =
        C ^ 2 * sqrtRb ^ 2 * (q ^ 2 * (2 : ℝ) ^ r) / 4 by ring]
    rw [h_sqrt_sq, h_q_sq_2pow_r]
  -- Bound: (2^b)² ≥ 4k².
  have h_2pow_b_sq_ge : ((2 : ℝ) ^ (apssvB k)) ^ 2 ≥ 4 * (k : ℝ) ^ 2 := by
    have h_2pow_b_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (apssvB k) := by positivity
    have h_2k_nn : (0 : ℝ) ≤ 2 * k := by positivity
    have := mul_self_le_mul_self h_2k_nn h_2k_le_2pow_b
    nlinarith
  have h_4pik_sq_pos : (0 : ℝ) < 64 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
  -- exp_arg = -(τ/2)² · 2^r / (64π²k²) ≤ -C²(r+b)/(64π²).
  have h_exp_arg_le : -((C * sqrtRb * q / 2) ^ 2 * (2 : ℝ) ^ r)
        / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2) ≤
      -C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) := by
    -- Step 1: substitute exact value of LHS numerator.
    rw [h_τ_sq_2pow_r_eq]
    -- Goal: -(C²·(r+b)·(2^b)² / 4) / (64π²k²) ≤ -C²·(r+b)/(64π²)
    -- ⟺ C²·(r+b)·(2^b)² / (4·64π²k²) ≥ C²·(r+b)/(64π²)  (negation flip)
    -- ⟺ (2^b)² / (4k²) ≥ 1  (dividing by C²(r+b)/(64π²) > 0)
    -- ⟺ (2^b)² ≥ 4k². ✓
    have h_step : C ^ 2 * ((r : ℝ) + apssvB k) * ((2 : ℝ) ^ (apssvB k)) ^ 2 / 4 /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2) ≥
        C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) := by
      have h_C_sq_nn : 0 ≤ C ^ 2 := sq_nonneg _
      have h_rb_nn : 0 ≤ (r : ℝ) + apssvB k := h_sum_pos.le
      have h_64pi_sq_pos : (0 : ℝ) < 64 * Real.pi ^ 2 := by positivity
      have h_k_sq_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      have h_factor_nn : 0 ≤ C ^ 2 * ((r : ℝ) + apssvB k) := mul_nonneg h_C_sq_nn h_rb_nn
      -- Reduce to showing (2^b)² / (4 · k²) ≥ 1, i.e., (2^b)² ≥ 4 k².
      have h_4ksq_le : 4 * (k : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (apssvB k)) ^ 2 := h_2pow_b_sq_ge
      have h_rewrite_lhs : C ^ 2 * ((r : ℝ) + apssvB k) *
          ((2 : ℝ) ^ (apssvB k)) ^ 2 / 4 / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)
          = C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) *
            (((2 : ℝ) ^ (apssvB k)) ^ 2 / (4 * (k : ℝ) ^ 2)) := by
        field_simp
      rw [h_rewrite_lhs]
      have h_factor : 0 ≤ C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) := by
        apply div_nonneg h_factor_nn h_64pi_sq_pos.le
      have h_ratio_ge_one :
          1 ≤ ((2 : ℝ) ^ (apssvB k)) ^ 2 / (4 * (k : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have :
          C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) * 1 ≤
          C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) *
            (((2 : ℝ) ^ (apssvB k)) ^ 2 / (4 * (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_ratio_ge_one h_factor
      simpa using this
    -- Step 2: convert h_step (≥) into the goal (≤ with negation).
    -- Goal: -(C²·(r+b)·(2^b)²/4) / (64π²k²) ≤ -C²·(r+b)/(64π²)
    -- Equivalently: -(LHS) ≤ -(RHS) ⟺ RHS ≤ LHS (where LHS, RHS are the positive parts of h_step).
    have h_neg_div_eq : -(C ^ 2 * ((r : ℝ) + apssvB k) * ((2 : ℝ) ^ (apssvB k)) ^ 2 / 4) /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2) =
        -(C ^ 2 * ((r : ℝ) + apssvB k) * ((2 : ℝ) ^ (apssvB k)) ^ 2 / 4 /
          (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) := by
      ring
    have h_neg_eq : -C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2) =
        -(C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) := by ring
    rw [h_neg_div_eq, h_neg_eq]
    exact neg_le_neg h_step
  -- Now bound prefactor: 8πk/(C·sqrt·q) ≤ 8π·2^(r/2)/C.
  -- Need: k/(C·sqrt·q) ≤ 2^(r/2)/C ⟺ k ≤ 2^(r/2)·sqrt·q.
  -- Since 2k ≤ 2^b (i.e., k ≤ 2^(b-1)), and sqrt ≥ 1, q = 2^(b-r/2):
  --   2^(r/2) · q = 2^(r/2) · 2^(b-r/2) = 2^b ≥ 2k > k. ✓
  have h_p_q_eq : p * q = (2 : ℝ) ^ (apssvB k) := by
    rw [h_p_def, h_q_def, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (r : ℝ) / 2 + ((apssvB k : ℝ) - (r : ℝ) / 2) = (apssvB k : ℝ) by ring,
        Real.rpow_natCast]
  -- We want: 8πk/(C·sqrt·q) ≤ 8π·p/C.
  -- Equivalent: k/(C·sqrt·q) ≤ p/C, i.e., k·C ≤ (C·sqrt·q)·p = C·sqrt·(p·q) = C·sqrt·2^b.
  -- Cancellation: k ≤ sqrt·2^b. Suffices k ≤ 2^b (via sqrt ≥ 1) and k ≤ 2^b is from 2k ≤ 2^b.
  have h_pi_nn : 0 ≤ 8 * Real.pi := by have := Real.pi_pos; linarith
  have h_C_nn : 0 ≤ C := hC.le
  have h_p_nn : 0 ≤ p := h_p_pos.le
  have h_q_nn : 0 ≤ q := h_q_pos.le
  have h_sqrt_nn : 0 ≤ sqrtRb := h_sqrt_pos.le
  have h_2pow_b_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (apssvB k) := by positivity
  -- Step A: k ≤ sqrtRb · 2^b.
  have h_k_le_sqrt_b : (k : ℝ) ≤ sqrtRb * (2 : ℝ) ^ (apssvB k) := by
    have h_k_le_b : (k : ℝ) ≤ (2 : ℝ) ^ (apssvB k) := by linarith
    have h_one_le : (1 : ℝ) * (2 : ℝ) ^ (apssvB k) ≤ sqrtRb * (2 : ℝ) ^ (apssvB k) :=
      mul_le_mul_of_nonneg_right h_sqrt_ge_one h_2pow_b_nn
    have h_one_mul : (1 : ℝ) * (2 : ℝ) ^ (apssvB k) = (2 : ℝ) ^ (apssvB k) := one_mul _
    linarith
  -- Step B: 8πk·C ≤ 8π·sqrt·2^b·C
  have h_step1 : 8 * Real.pi * (k : ℝ) * C ≤
      8 * Real.pi * (sqrtRb * (2 : ℝ) ^ (apssvB k)) * C := by
    have h_lhs : 8 * Real.pi * (k : ℝ) ≤ 8 * Real.pi * (sqrtRb * (2 : ℝ) ^ (apssvB k)) :=
      mul_le_mul_of_nonneg_left h_k_le_sqrt_b h_pi_nn
    exact mul_le_mul_of_nonneg_right h_lhs h_C_nn
  -- Step C: combine to k·C ≤ (C·sqrt·q)·p, since p·q = 2^b.
  have h_pre_le : 8 * Real.pi * (k : ℝ) / (C * sqrtRb * q) ≤
      8 * Real.pi * p / C := by
    rw [div_le_div_iff₀ h_τ hC]
    -- Goal: 8πk·C ≤ 8π·p·(C·sqrt·q)
    -- We have 8πk·C ≤ 8π·sqrt·2^b·C = 8π·sqrt·(p·q)·C = 8π·p·sqrt·q·C = 8π·p·(C·sqrt·q)
    have h_rewrite_target : 8 * Real.pi * p * (C * sqrtRb * q) =
        8 * Real.pi * (sqrtRb * (p * q)) * C := by ring
    rw [h_rewrite_target, h_p_q_eq]
    exact h_step1
  have h_pre_add_le : 8 * Real.pi * (k : ℝ) / (C * sqrtRb * q) + 4 ≤
      8 * Real.pi * p / C + 4 := by linarith
  -- exp factor in goal is ≤ exp(-C²(r+b)/(64π²)) which is the long envelope's exp.
  have h_exp_le : Real.exp (-((C * sqrtRb * q / 2) ^ 2 * (2 : ℝ) ^ r) /
        (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) ≤
      Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) :=
    Real.exp_le_exp.mpr h_exp_arg_le
  have h_exp_long_pos : 0 < Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) :=
    Real.exp_pos _
  have h_4exp_le : 4 * Real.exp (-((C * sqrtRb * q / 2) ^ 2 * (2 : ℝ) ^ r) /
        (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)) ≤
      4 * Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) :=
    mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
  have h_pre_C_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / (C * sqrtRb * q) + 4 := by
    have h_div_nn : 0 ≤ 8 * Real.pi * (k : ℝ) / (C * sqrtRb * q) := by
      apply div_nonneg
      · positivity
      · exact h_τ.le
    linarith
  have h_4exp_long_nn : 0 ≤ 4 * Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) := by
    linarith
  -- Combine.
  unfold apssvLongEnvelope
  rw [if_pos ⟨hk, hC⟩]
  rw [show (8 * Real.pi * p / C + 4) * 4 *
        Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2)) =
        (8 * Real.pi * p / C + 4) *
        (4 * Real.exp (-C ^ 2 * ((r : ℝ) + apssvB k) / (64 * Real.pi ^ 2))) by ring]
  exact mul_le_mul h_pre_add_le h_4exp_le
    (by positivity) (by linarith)

/-- Combined pointwise envelope domination:
`apssvRegimeSplitBoundReal C k r ≤ apssvShortEnvelope C k r + apssvLongEnvelope C k r`. -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_le_envelope_sum (C : ℝ) (k r : ℕ) :
    apssvRegimeSplitBoundReal C k r ≤
      apssvShortEnvelope C k r + apssvLongEnvelope C k r := by
  by_cases h : 1 ≤ k ∧ 0 < C
  · obtain ⟨hk, hC⟩ := h
    -- Active branch: apssvRegimeSplitBoundReal = min(M2, lin).
    unfold apssvRegimeSplitBoundReal
    rw [dif_pos ⟨hk, hC⟩]
    -- Case split on r ≤ b vs r > b.
    by_cases hr : r ≤ apssvB k
    · -- Short regime: min ≤ M2 ≤ shortEnv. longEnv ≥ 0.
      have h_M2_le := apssv_M2_term_le_short_envelope C hC k r hk hr
      have h_long_nn := apssvLongEnvelope_nonneg C k r
      have h_min_le_left := min_le_left
        ((8 * Real.pi * (k : ℝ) / (C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
            (4 * Real.exp (-(C * Real.sqrt ((r : ℝ) + apssvB k) *
              min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 /
                (16 * (2 : ℝ) ^ r))))
        ((8 * Real.pi * (k : ℝ) / (C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
            (4 * Real.exp (-((C * Real.sqrt ((r : ℝ) + apssvB k) *
              min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 *
              (2 : ℝ) ^ r) / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))))
      linarith
    · -- Long regime: min ≤ lin ≤ longEnv. shortEnv ≥ 0.
      push_neg at hr  -- hr : apssvB k < r
      have h_lin_le := apssv_linear_term_le_long_envelope C hC k r hk hr
      have h_short_nn := apssvShortEnvelope_nonneg C k r
      have h_min_le_right := min_le_right
        ((8 * Real.pi * (k : ℝ) / (C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
            (4 * Real.exp (-(C * Real.sqrt ((r : ℝ) + apssvB k) *
              min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 /
                (16 * (2 : ℝ) ^ r))))
        ((8 * Real.pi * (k : ℝ) / (C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
            (4 * Real.exp (-((C * Real.sqrt ((r : ℝ) + apssvB k) *
              min ((2 : ℝ) ^ ((r : ℝ) / 2)) ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 *
              (2 : ℝ) ^ r) / (64 * Real.pi ^ 2 * (k : ℝ) ^ 2))))
      linarith
  · -- Inactive branch: apssvRegimeSplitBoundReal = 0 ≤ 0 + 0 ≤ shortEnv + longEnv.
    unfold apssvRegimeSplitBoundReal
    rw [dif_neg h]
    have h_short_nn := apssvShortEnvelope_nonneg C k r
    have h_long_nn := apssvLongEnvelope_nonneg C k r
    linarith

/-- Conversion: `2^(apssvB k) ≤ 4k` for `k ≥ 1`. -/
@[category API, AMS 11]
lemma apssv_two_pow_b_le (k : ℕ) (hk : 1 ≤ k) : (2 : ℝ) ^ (apssvB k : ℝ) ≤ 4 * k := by
  unfold apssvB
  rw [Real.rpow_natCast]
  rw [pow_succ]
  have h2k_ne : 2 * k ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (Nat.one_le_iff_ne_zero.mp hk)
  have h_log_nat : (2 : ℕ) ^ Nat.log2 (2 * k) ≤ 2 * k := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 h2k_ne
  have h_log_real : ((2 : ℝ) ^ Nat.log2 (2 * k)) ≤ 2 * (k : ℝ) := by
    have := h_log_nat
    push_cast [show ((2 : ℕ) ^ Nat.log2 (2 * k) : ℝ) = (2 : ℝ) ^ Nat.log2 (2 * k) from by
      push_cast; ring] at this
    exact_mod_cast this
  nlinarith [h_log_real, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.log2 (2*k))]

/-- **Focused real-analysis sub-claim 1**: for `C ≥ 100`, the short-regime
envelope `apssvShortEnvelope C` is summable on `(k, r) ∈ ℕ × ℕ`.

Geometric-series bound: with `A := exp(-C²/64) < 1` (for `C ≥ 100`,
`A < exp(-156)` is tiny), the short envelope decays as
`(constant)·2^b(k)·A^r·A^b(k)` summed over `(k, r)`.
* The `r`-sum is geometric: `∑_r A^r = 1/(1-A)`.
* The `k`-sum: `∑_k 2^b(k)·A^b(k)` with `2^b(k) ≤ 4k` and
  `b(k) ≥ log₂(2k)`, giving `∑_k 4k·(2A)^b(k)` polynomial decay
  (since `2·exp(-C²/64) < 1` for `C ≥ 10`). -/
@[category API, AMS 11]
lemma apssvShortEnvelope_summable_at_C100 :
    Summable (fun kr : ℕ × ℕ => apssvShortEnvelope 100 kr.1 kr.2) := by
  -- Set α := 100²/64 = 156.25.
  set α : ℝ := (100 : ℝ)^2 / 64 with hα_def
  have hα_pos : 0 < α := by simp only [hα_def]; norm_num
  have hα_ge : (4 : ℝ) * Real.log 2 ≤ α := by
    -- α = 156.25, 4 · log 2 ≈ 2.77.
    have h_log2_lt : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
      linarith
    simp only [hα_def]
    nlinarith [h_log2_lt, Real.log_pos (by norm_num : (1:ℝ) < 2)]
  -- Factor: apssvShortEnvelope 100 k r = f_short k * g_short r where
  -- f_short k = (8π·2^b/100 + 4)·4·exp(-α·b)  (or 0 for k = 0)
  -- g_short r = exp(-α·r)
  -- Define f and g.
  set f : ℕ → ℝ := fun k =>
    if 1 ≤ k then
      (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / 100 + 4) * 4 *
        Real.exp (-α * (apssvB k))
    else 0 with hf_def
  set g : ℕ → ℝ := fun r => Real.exp (-α * r) with hg_def
  -- Step 1: factorization.
  have h_factor : ∀ kr : ℕ × ℕ,
      apssvShortEnvelope 100 kr.1 kr.2 = f kr.1 * g kr.2 := by
    rintro ⟨k, r⟩
    show apssvShortEnvelope 100 k r = f k * g r
    by_cases hk : 1 ≤ k
    · -- Active case.
      have h_short : apssvShortEnvelope 100 k r =
          (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / 100 + 4) * 4 *
            Real.exp (-(100:ℝ)^2 * ((r : ℝ) + apssvB k) / 64) := by
        unfold apssvShortEnvelope
        rw [if_pos ⟨hk, by norm_num⟩]
      rw [h_short]
      have h_f : f k = (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / 100 + 4) * 4 *
            Real.exp (-α * apssvB k) := by
        simp only [hf_def, if_pos hk]
      have h_g : g r = Real.exp (-α * r) := by simp only [hg_def]
      rw [h_f, h_g]
      -- exp(-100²·(r+b)/64) = exp(-α·b) · exp(-α·r)
      have h_exp_split :
          Real.exp (-(100:ℝ)^2 * ((r : ℝ) + apssvB k) / 64) =
            Real.exp (-α * apssvB k) * Real.exp (-α * r) := by
        rw [← Real.exp_add]
        congr 1
        simp only [hα_def]
        ring
      rw [h_exp_split]
      ring
    · have h_short : apssvShortEnvelope 100 k r = 0 := by
        unfold apssvShortEnvelope
        rw [if_neg]
        intro ⟨hk', _⟩
        exact hk hk'
      have h_f : f k = 0 := by simp only [hf_def, if_neg hk]
      rw [h_short, h_f]
      ring
  -- Step 2: nonneg.
  have h_f_nn : ∀ k, 0 ≤ f k := by
    intro k
    simp only [hf_def]
    by_cases hk : 1 ≤ k
    · simp only [hk, if_pos]
      have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (apssvB k) := by positivity
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_pre_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) / 100 + 4 := by
        have : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ (apssvB k) / 100 := by positivity
        linarith
      have h_exp_nn : 0 ≤ Real.exp (-α * apssvB k) := (Real.exp_pos _).le
      positivity
    · simp only [hk, if_false]; rfl
  have h_g_nn : ∀ r, 0 ≤ g r := fun r => (Real.exp_pos _).le
  -- Step 3: g is summable (geometric).
  have h_g_summable : Summable g := by
    simp only [hg_def]
    -- exp(-α · r) = exp(-α)^r and exp(-α) < 1 (since α > 0).
    have : Summable (fun r : ℕ => Real.exp ((r : ℝ) * (-α))) :=
      Real.summable_exp_nat_mul_iff.mpr (by linarith : -α < 0)
    convert this using 1
    ext r
    ring_nf
  -- Step 4: f is summable, dominated by 4/k^3.
  -- Bound: for k ≥ 1, f k ≤ 4/k^3.
  have h_f_bound : ∀ k, f k ≤ 4 / (k : ℝ)^3 := by
    intro k
    by_cases hk : 1 ≤ k
    · -- k ≥ 1 case: prove the actual bound.
      simp only [hf_def, hk, if_pos]
      have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
      have h_b_pos : 0 < apssvB k := by unfold apssvB; omega
      have h_b_real_pos : (0 : ℝ) < (apssvB k : ℝ) := by exact_mod_cast h_b_pos
      -- 2k ≤ 2^b
      have h_2k_le : (2 * k : ℝ) ≤ (2 : ℝ) ^ (apssvB k) :=
        apssv_two_k_le_two_pow_b_real k
      -- exp(-α·b) ≤ 1/(16 k^4) using α ≥ 4·log 2 and 2^b ≥ 2k.
      -- We have (2:ℝ)^(b:ℕ) = exp(b·log 2). So 2^(4b) = exp(4b·log 2) ≤ exp(α·b).
      -- Hence exp(-α·b) ≤ 2^(-4b) = 1/2^(4b) ≤ 1/(2k)^4 = 1/(16 k^4).
      have h_exp_le : Real.exp (-α * (apssvB k)) ≤ 1 / (16 * (k : ℝ)^4) := by
        -- Step a: exp(-α·b) ≤ exp(-(4·log 2)·b) = 2^(-4b) (in real-power sense).
        have h_step_a : Real.exp (-α * (apssvB k)) ≤
            Real.exp (-(4 * Real.log 2) * (apssvB k)) := by
          apply Real.exp_le_exp.mpr
          have h_b_nn : (0 : ℝ) ≤ (apssvB k : ℝ) := h_b_real_pos.le
          have : -α ≤ -(4 * Real.log 2) := by linarith
          nlinarith [this, h_b_nn]
        -- Step b: exp(-(4·log 2)·b) = 1/2^(4b).
        have h_step_b : Real.exp (-(4 * Real.log 2) * (apssvB k)) =
            1 / (2 : ℝ) ^ (4 * apssvB k) := by
          -- exp(b · log 2) = 2^b, so exp(-(4·log 2)·b) = 1 / 2^(4b).
          have h_exp_log : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
          have h_pow_eq : (2 : ℝ) ^ (4 * apssvB k) =
              Real.exp (((4 * apssvB k : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, h_exp_log]
          rw [h_pow_eq]
          rw [show -(4 * Real.log 2) * (apssvB k : ℝ) =
                -(((4 * apssvB k : ℕ) : ℝ) * Real.log 2) by
                push_cast; ring]
          rw [Real.exp_neg]
          rw [one_div]
        -- Step c: 1/2^(4b) ≤ 1/(16 k^4) since 2k ≤ 2^b ⇒ (2k)^4 ≤ 2^(4b).
        have h_step_c : (1 : ℝ) / (2 : ℝ) ^ (4 * apssvB k) ≤ 1 / (16 * (k:ℝ)^4) := by
          have h_2k_pos : (0 : ℝ) < 2 * k := by linarith
          have h_2k4_le : (2 * (k:ℝ))^4 ≤ ((2:ℝ)^(apssvB k))^4 := by
            apply pow_le_pow_left₀ h_2k_pos.le h_2k_le
          have h_pow_eq : ((2:ℝ)^(apssvB k))^4 = (2:ℝ)^(4 * apssvB k) := by
            rw [← pow_mul]; ring_nf
          rw [h_pow_eq] at h_2k4_le
          have h_pow_pos : (0 : ℝ) < (2:ℝ)^(4 * apssvB k) := by positivity
          have h_rhs_pos : (0 : ℝ) < 16 * (k:ℝ)^4 := by positivity
          have h_2k4 : (2 * (k:ℝ))^4 = 16 * (k:ℝ)^4 := by ring
          rw [h_2k4] at h_2k4_le
          rw [div_le_div_iff₀ h_pow_pos h_rhs_pos]
          linarith
        calc Real.exp (-α * (apssvB k))
            ≤ Real.exp (-(4 * Real.log 2) * (apssvB k)) := h_step_a
          _ = 1 / (2 : ℝ) ^ (4 * apssvB k) := h_step_b
          _ ≤ 1 / (16 * (k:ℝ)^4) := h_step_c
      -- Now bound f k.
      -- f k = (8π·2^b/100 + 4) · 4 · exp(-α·b)
      --     = 32π·2^b·exp(-α·b)/100 + 16·exp(-α·b)
      -- Use 2^b ≤ 4k and exp(-α·b) ≤ 1/(16k^4).
      have h_2pow_b_le : (2:ℝ)^(apssvB k) ≤ 4 * k := by
        have h := apssv_two_pow_b_le k hk
        rwa [Real.rpow_natCast] at h
      have h_2pow_b_pos : (0 : ℝ) < (2:ℝ)^(apssvB k) := by positivity
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_exp_pos : 0 < Real.exp (-α * (apssvB k)) := Real.exp_pos _
      -- Distribute and estimate.
      calc (8 * Real.pi * (2 : ℝ) ^ (apssvB k) / 100 + 4) * 4 *
              Real.exp (-α * (apssvB k))
          = (8 * Real.pi * (2:ℝ)^(apssvB k) / 100) * 4 * Real.exp (-α * (apssvB k)) +
            16 * Real.exp (-α * (apssvB k)) := by ring
        _ ≤ (8 * Real.pi * (4 * k) / 100) * 4 * Real.exp (-α * (apssvB k)) +
            16 * (1 / (16 * (k:ℝ)^4)) := by
            have h_pre : 0 ≤ Real.pi := Real.pi_pos.le
            have h_exp_pos' : 0 < Real.exp (-α * (apssvB k)) := Real.exp_pos _
            gcongr
        _ = 32 * Real.pi * (k:ℝ) / 25 * Real.exp (-α * (apssvB k)) + 1 / (k:ℝ)^4 := by
            ring
        _ ≤ 32 * Real.pi * (k:ℝ) / 25 * (1 / (16 * (k:ℝ)^4)) + 1 / (k:ℝ)^4 := by
            have h_pre : 0 ≤ 32 * Real.pi * (k:ℝ) / 25 := by
              have : 0 ≤ Real.pi := Real.pi_pos.le
              positivity
            gcongr
        _ = (2 * Real.pi) / (25 * (k:ℝ)^3) + 1 / (k:ℝ)^4 := by
            field_simp
            ring
        _ ≤ 1 / (k:ℝ)^3 + 1 / (k:ℝ)^3 := by
            have hk3_pos : 0 < (k:ℝ)^3 := by positivity
            have hk4_pos : 0 < (k:ℝ)^4 := by positivity
            have h_pi_lt_4 : Real.pi < 4 := Real.pi_lt_four
            have h1 : (2 * Real.pi) / (25 * (k:ℝ)^3) ≤ 1 / (k:ℝ)^3 := by
              rw [div_le_div_iff₀ (by positivity) hk3_pos]
              nlinarith [Real.pi_pos]
            have h2 : 1 / (k:ℝ)^4 ≤ 1 / (k:ℝ)^3 := by
              rw [div_le_div_iff₀ hk4_pos hk3_pos]
              have hk_ge_one : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
              nlinarith [hk_ge_one]
            linarith
        _ ≤ 4 / (k:ℝ)^3 := by
            have hk3_pos : 0 < (k:ℝ)^3 := by positivity
            have h_inv_pos : 0 < (1 : ℝ) / (k:ℝ)^3 := by positivity
            rw [show (4 : ℝ) / (k:ℝ)^3 = 4 * (1 / (k:ℝ)^3) by ring]
            linarith [h_inv_pos]
    · simp only [hf_def, hk, if_false]
      have : (0:ℝ) ≤ 4 / (k:ℝ)^3 := by
        push_neg at hk
        interval_cases k
        simp
      linarith
  have h_dominator_summable : Summable (fun k : ℕ => 4 / (k : ℝ)^3) := by
    have h_base : Summable (fun n : ℕ => 1 / (n : ℝ)^3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    have h_scaled := h_base.mul_left (4 : ℝ)
    convert h_scaled using 1
    ext k; ring
  have h_f_summable : Summable f :=
    h_dominator_summable.of_nonneg_of_le h_f_nn h_f_bound
  -- Step 5: Combine via Summable.mul_of_nonneg.
  have h_prod_summable :
      Summable (fun kr : ℕ × ℕ => f kr.1 * g kr.2) :=
    Summable.mul_of_nonneg h_f_summable h_g_summable h_f_nn h_g_nn
  -- Convert via factorization.
  exact h_prod_summable.congr (fun kr => (h_factor kr).symm)

/-- **Focused real-analysis sub-claim 2**: for `C ≥ 100`, the long-regime
envelope `apssvLongEnvelope C` is summable on `(k, r) ∈ ℕ × ℕ`.

Geometric-series bound: the long envelope is
`(8π·2^(r/2)/C + 4)·4·exp(-C²(r+b)/(64π²))`. With `B := exp(-C²/(64π²))`
and ratio `√2·B`, the `r`-sum converges (ratio < 1 for `C ≥ 100`,
where `√2·exp(-15.83) ≪ 1`). The `k`-sum has `B^b(k)` decay summable
as before. -/
@[category API, AMS 11]
lemma apssvLongEnvelope_summable_at_C100 :
    Summable (fun kr : ℕ × ℕ => apssvLongEnvelope 100 kr.1 kr.2) := by
  -- Set α' := 100²/(64π²) ≈ 15.83.
  set α : ℝ := (100 : ℝ)^2 / (64 * Real.pi^2) with hα_def
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt_4 : Real.pi < 4 := Real.pi_lt_four
  have h_pi_sq_pos : 0 < Real.pi^2 := by positivity
  have hα_pos : 0 < α := by
    simp only [hα_def]
    positivity
  -- α ≥ 3·log 2 (needed for k decay).
  have h_log2_lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    linarith
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hα_ge_3log2 : (3 : ℝ) * Real.log 2 ≤ α := by
    -- 3 log 2 ≤ 3 < 100²/(64π²). Need 192π² < 10000/log 2.
    -- π² < 16, so 192·16 = 3072 < 10000. Suffices.
    simp only [hα_def]
    have h_pi_sq_lt_16 : Real.pi^2 < 16 := by nlinarith [h_pi_lt_4, Real.pi_pos]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h_pi_sq_lt_16, h_pi_sq_pos, h_log2_lt, h_log2_pos]
  -- α ≥ 1 + log 2 / 2 (needed for r decay).
  have hα_ge_one : (1 : ℝ) + Real.log 2 / 2 ≤ α := by
    -- 1 + log 2 / 2 < 2 < α.
    have hα_ge_2 : (2 : ℝ) ≤ α := by
      simp only [hα_def]
      have h_pi_sq_lt_16 : Real.pi^2 < 16 := by nlinarith [h_pi_lt_4, Real.pi_pos]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h_pi_sq_lt_16, h_pi_sq_pos]
    linarith
  -- Define f(k) = exp(-α·b(k)) for k ≥ 1, else 0; g(r) = (8π·2^(r/2)/100 + 4)·4·exp(-α·r).
  set f : ℕ → ℝ := fun k =>
    if 1 ≤ k then Real.exp (-α * (apssvB k))
    else 0 with hf_def
  set g : ℕ → ℝ := fun r =>
    (8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / 100 + 4) * 4 *
      Real.exp (-α * r) with hg_def
  -- Step 1: factorization.
  have h_factor : ∀ kr : ℕ × ℕ,
      apssvLongEnvelope 100 kr.1 kr.2 = f kr.1 * g kr.2 := by
    rintro ⟨k, r⟩
    show apssvLongEnvelope 100 k r = f k * g r
    by_cases hk : 1 ≤ k
    · have h_long : apssvLongEnvelope 100 k r =
          (8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / 100 + 4) * 4 *
            Real.exp (-(100:ℝ)^2 * ((r : ℝ) + apssvB k) / (64 * Real.pi^2)) := by
        unfold apssvLongEnvelope
        rw [if_pos ⟨hk, by norm_num⟩]
      rw [h_long]
      have h_f : f k = Real.exp (-α * apssvB k) := by simp only [hf_def, if_pos hk]
      have h_g : g r = (8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / 100 + 4) * 4 *
            Real.exp (-α * r) := by simp only [hg_def]
      rw [h_f, h_g]
      have h_exp_split :
          Real.exp (-(100:ℝ)^2 * ((r : ℝ) + apssvB k) / (64 * Real.pi^2)) =
            Real.exp (-α * apssvB k) * Real.exp (-α * r) := by
        rw [← Real.exp_add]
        congr 1
        simp only [hα_def]
        field_simp
        ring
      rw [h_exp_split]
      ring
    · have h_long : apssvLongEnvelope 100 k r = 0 := by
        unfold apssvLongEnvelope
        rw [if_neg]
        intro ⟨hk', _⟩
        exact hk hk'
      have h_f : f k = 0 := by simp only [hf_def, if_neg hk]
      rw [h_long, h_f]
      ring
  -- Step 2: nonneg.
  have h_f_nn : ∀ k, 0 ≤ f k := by
    intro k
    simp only [hf_def]
    by_cases hk : 1 ≤ k
    · simp only [hk, if_pos]; exact (Real.exp_pos _).le
    · simp only [hk, if_false]; rfl
  have h_g_nn : ∀ r, 0 ≤ g r := by
    intro r
    simp only [hg_def]
    have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_pre_nn : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / 100 + 4 := by
      have : 0 ≤ 8 * Real.pi * (2 : ℝ) ^ ((r : ℝ) / 2) / 100 := by positivity
      linarith
    have h_exp_nn : 0 ≤ Real.exp (-α * r) := (Real.exp_pos _).le
    positivity
  -- Step 3: g is summable, dominated by 18 · exp(-r).
  have h_g_bound : ∀ r, g r ≤ 18 * Real.exp (-(r : ℝ)) := by
    intro r
    simp only [hg_def]
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_2pow_log : Real.log ((2 : ℝ) ^ ((r : ℝ) / 2)) = ((r : ℝ) / 2) * Real.log 2 := by
      rw [Real.log_rpow (by norm_num)]
    -- Rewrite 2^(r/2) = exp((r/2) · log 2).
    have h_2pow_eq : (2 : ℝ) ^ ((r : ℝ) / 2) = Real.exp ((r : ℝ) / 2 * Real.log 2) := by
      rw [show ((r : ℝ) / 2 * Real.log 2 : ℝ) = Real.log ((2 : ℝ) ^ ((r : ℝ) / 2)) by
        rw [h_2pow_log]]
      rw [Real.exp_log h_2pow_pos]
    rw [h_2pow_eq]
    -- Now: (8π · exp((r/2)·log 2) / 100 + 4) · 4 · exp(-α·r)
    --    = (32π/100) · exp((r/2)·log 2) · exp(-α·r) + 16 · exp(-α·r)
    --    = (32π/100) · exp(-(α - log 2/2)·r) + 16 · exp(-α·r)
    -- We need this ≤ 18 · exp(-r), i.e., bound by exp(-r) using α ≥ 1 + log 2 / 2.
    have h_exp_combine : Real.exp ((r : ℝ) / 2 * Real.log 2) * Real.exp (-α * r) =
        Real.exp (-((α - Real.log 2 / 2) * r)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_first :
        (8 * Real.pi * Real.exp ((r : ℝ) / 2 * Real.log 2) / 100 + 4) * 4 *
            Real.exp (-α * r) =
        (32 * Real.pi / 100) * Real.exp (-((α - Real.log 2 / 2) * r)) +
          16 * Real.exp (-α * r) := by
      have : (8 * Real.pi * Real.exp ((r : ℝ) / 2 * Real.log 2) / 100 + 4) * 4 *
              Real.exp (-α * r) =
          (32 * Real.pi / 100) *
            (Real.exp ((r : ℝ) / 2 * Real.log 2) * Real.exp (-α * r)) +
          16 * Real.exp (-α * r) := by ring
      rw [this, h_exp_combine]
    rw [h_first]
    -- Now bound (32π/100)·exp(-(α-log2/2)·r) + 16·exp(-α·r) ≤ 18·exp(-r).
    have h_exp_r_bound1 : Real.exp (-((α - Real.log 2 / 2) * r)) ≤ Real.exp (-(r : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h_α_ge : 1 ≤ α - Real.log 2 / 2 := by linarith
      nlinarith [h_α_ge, hr_nn]
    have h_exp_r_bound2 : Real.exp (-α * r) ≤ Real.exp (-(r : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h_α_ge : 1 ≤ α := by linarith
      nlinarith [h_α_ge, hr_nn]
    have h_pi_le : 32 * Real.pi / 100 ≤ 2 := by
      nlinarith [h_pi_lt_4, h_pi_pos]
    have h_first_le : (32 * Real.pi / 100) * Real.exp (-((α - Real.log 2 / 2) * r)) ≤
        2 * Real.exp (-(r : ℝ)) := by
      have h_exp_pos : 0 < Real.exp (-((α - Real.log 2 / 2) * r)) := Real.exp_pos _
      have h_exp_r_pos : 0 < Real.exp (-(r : ℝ)) := Real.exp_pos _
      calc (32 * Real.pi / 100) * Real.exp (-((α - Real.log 2 / 2) * r))
          ≤ (32 * Real.pi / 100) * Real.exp (-(r : ℝ)) := by
            have h_pi_nn : 0 ≤ 32 * Real.pi / 100 := by positivity
            exact mul_le_mul_of_nonneg_left h_exp_r_bound1 h_pi_nn
        _ ≤ 2 * Real.exp (-(r : ℝ)) := by
            exact mul_le_mul_of_nonneg_right h_pi_le h_exp_r_pos.le
    have h_second_le : 16 * Real.exp (-α * r) ≤ 16 * Real.exp (-(r : ℝ)) := by
      exact mul_le_mul_of_nonneg_left h_exp_r_bound2 (by norm_num)
    linarith
  -- g summable: dominated by 18 · exp(-r), which is geometric.
  have h_exp_neg_summable : Summable (fun r : ℕ => Real.exp (-(r : ℝ))) := by
    have : Summable (fun r : ℕ => Real.exp ((r : ℝ) * (-1))) :=
      Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-1:ℝ) < 0)
    convert this using 1
    ext r; ring_nf
  have h_g_summable : Summable g := by
    have h_dom : Summable (fun r : ℕ => 18 * Real.exp (-(r : ℝ))) :=
      h_exp_neg_summable.mul_left 18
    exact h_dom.of_nonneg_of_le h_g_nn h_g_bound
  -- Step 4: f summable, dominated by 1/(8 k^3).
  have h_f_bound : ∀ k, f k ≤ 1 / (8 * (k : ℝ)^3) := by
    intro k
    by_cases hk : 1 ≤ k
    · simp only [hf_def, hk, if_pos]
      have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
      have h_b_pos : 0 < apssvB k := by unfold apssvB; omega
      have h_b_real_pos : (0 : ℝ) < (apssvB k : ℝ) := by exact_mod_cast h_b_pos
      have h_2k_le : (2 * k : ℝ) ≤ (2 : ℝ) ^ (apssvB k) :=
        apssv_two_k_le_two_pow_b_real k
      -- exp(-α·b) ≤ exp(-(3·log 2)·b) = 1/2^(3b) ≤ 1/(2k)^3 = 1/(8k^3).
      have h_step_a : Real.exp (-α * (apssvB k)) ≤
          Real.exp (-(3 * Real.log 2) * (apssvB k)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hα_ge_3log2, h_b_real_pos]
      have h_exp_log : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
      have h_step_b : Real.exp (-(3 * Real.log 2) * (apssvB k)) =
          1 / (2 : ℝ) ^ (3 * apssvB k) := by
        have h_pow_eq : (2 : ℝ) ^ (3 * apssvB k) =
            Real.exp (((3 * apssvB k : ℕ) : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, h_exp_log]
        rw [h_pow_eq]
        rw [show -(3 * Real.log 2) * (apssvB k : ℝ) =
              -(((3 * apssvB k : ℕ) : ℝ) * Real.log 2) by
              push_cast; ring]
        rw [Real.exp_neg]
        rw [one_div]
      have h_step_c : (1 : ℝ) / (2 : ℝ) ^ (3 * apssvB k) ≤ 1 / (8 * (k : ℝ)^3) := by
        have h_2k_pos : (0 : ℝ) < 2 * k := by linarith
        have h_2k3_le : (2 * (k : ℝ))^3 ≤ ((2 : ℝ) ^ (apssvB k))^3 := by
          apply pow_le_pow_left₀ h_2k_pos.le h_2k_le
        have h_pow_eq : ((2 : ℝ) ^ (apssvB k))^3 = (2 : ℝ) ^ (3 * apssvB k) := by
          rw [← pow_mul]; ring_nf
        rw [h_pow_eq] at h_2k3_le
        have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (3 * apssvB k) := by positivity
        have h_rhs_pos : (0 : ℝ) < 8 * (k : ℝ)^3 := by positivity
        have h_2k3 : (2 * (k : ℝ))^3 = 8 * (k : ℝ)^3 := by ring
        rw [h_2k3] at h_2k3_le
        rw [div_le_div_iff₀ h_pow_pos h_rhs_pos]
        linarith
      calc Real.exp (-α * (apssvB k))
          ≤ Real.exp (-(3 * Real.log 2) * (apssvB k)) := h_step_a
        _ = 1 / (2 : ℝ) ^ (3 * apssvB k) := h_step_b
        _ ≤ 1 / (8 * (k : ℝ)^3) := h_step_c
    · simp only [hf_def, hk, if_false]
      push_neg at hk
      interval_cases k
      simp
  have h_f_summable : Summable f := by
    have h_dom : Summable (fun k : ℕ => 1 / (8 * (k : ℝ)^3)) := by
      have h_base : Summable (fun n : ℕ => 1 / (n : ℝ)^3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      have h_scaled := h_base.mul_left (1 / 8 : ℝ)
      convert h_scaled using 1
      ext k; ring
    exact h_dom.of_nonneg_of_le h_f_nn h_f_bound
  -- Step 5: combine.
  have h_prod_summable :
      Summable (fun kr : ℕ × ℕ => f kr.1 * g kr.2) :=
    Summable.mul_of_nonneg h_f_summable h_g_summable h_f_nn h_g_nn
  exact h_prod_summable.congr (fun kr => (h_factor kr).symm)

/-- Combined summability of `apssvRegimeSplitBoundReal` at `C = 100`. -/
@[category API, AMS 11]
lemma apssvRegimeSplitBoundReal_summable_at_C100 :
    Summable (fun kr : ℕ × ℕ => apssvRegimeSplitBoundReal 100 kr.1 kr.2) := by
  -- Dominate by sum of envelopes.
  have h_envelope_sum : Summable
      (fun kr : ℕ × ℕ => apssvShortEnvelope 100 kr.1 kr.2 +
        apssvLongEnvelope 100 kr.1 kr.2) :=
    apssvShortEnvelope_summable_at_C100.add apssvLongEnvelope_summable_at_C100
  apply h_envelope_sum.of_nonneg_of_le
    (fun kr => apssvRegimeSplitBoundReal_nonneg 100 kr.1 kr.2)
  intro kr
  exact apssvRegimeSplitBoundReal_le_envelope_sum 100 kr.1 kr.2

/-- **Residual real-analysis claim**: there exists `C > 0` such that the
double tsum of `ENNReal.ofReal` of the regime-split closed form is strictly
below `1`.

The discharge is via Tannery's dominated convergence theorem
(`tendsto_tsum_of_dominated_convergence`):

* Per-term tendsto (`apssvRegimeSplitBoundReal_tendsto_zero`): each entry
  tends to `0` as `C → ∞`.
* Dominator: the geometric envelope at the explicit witness `C₀ = 100` is
  summable in `(k, r) ∈ ℕ × ℕ` via
  `apssvRegimeSplitBoundReal_summable_at_C100`.
* Antitone in `C` (`apssvRegimeSplitBoundReal_antitone_on_pos`): for
  `0 < C₀ ≤ C`, `apssvRegimeSplitBoundReal C k r ≤
  apssvRegimeSplitBoundReal C₀ k r` (each of M=2 / linear is decreasing
  in `C`, so the `min` is too); hence the dominator dominates eventually.

Given those three ingredients, Tannery yields tsum-tendsto-zero, and a
final `Filter.Tendsto.eventually` extracts the witness `C` with sum `< 1`.

The geometric-summability argument: split `(k, r)` over short / long
regimes (`r ≤ b(k)` vs `r > b(k)`).  In short, M=2 gives
`exp(-C²(r+b)/64)`; in long, linear gives `exp(-C²(r+b)/(64π²))` after
`2^b ≥ 2k`.  Both regimes yield a doubly-geometric series in `(k, r)`
for `C` large enough.  Reformalizing this carefully is the next step.

**Refactor**: the structural decomposition is now in place via
`apssvRegimeSplitBoundReal_summable_at_C100` (which combines the
short/long envelope summability via `apssvRegimeSplitBoundReal_le_envelope_sum`).
Two focused sub-sorries remain: `apssvShortEnvelope_summable_at_C100` and
`apssvLongEnvelope_summable_at_C100`. -/
@[category API, AMS 11]
lemma apssv_regime_split_tsum_lt_one :
    ∃ C : ℝ, 0 < C ∧
      ∑' k : ℕ, ∑' r : ℕ, ENNReal.ofReal (apssvRegimeSplitBoundReal C k r) < 1 := by
  -- Refactored: the summability witness is now obtained from the structural
  -- decomposition `apssvRegimeSplitBoundReal_summable_at_C100`.
  have h_summable : ∃ C₀ > 0, Summable
      (fun kr : ℕ × ℕ => apssvRegimeSplitBoundReal C₀ kr.1 kr.2) :=
    ⟨100, by norm_num, apssvRegimeSplitBoundReal_summable_at_C100⟩
  -- ENNReal tsum tends to 0 as C → ∞.
  have h_tendsto := apssvRegimeSplitBoundReal_ennreal_tsum_tendsto_zero h_summable
  -- Eventually (in atTop), the sum is < 1.
  have h_eventually : ∀ᶠ C in Filter.atTop,
      ∑' k : ℕ, ∑' r : ℕ, ENNReal.ofReal (apssvRegimeSplitBoundReal C k r) < 1 :=
    h_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ENNReal) < 1))
  -- Combine with C > 0 to extract the witness.
  obtain ⟨C, hC_lt, hC_pos⟩ :=
    (h_eventually.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨C, hC_pos, hC_lt⟩

/- ## Existence of `C`: summation argument & main lemma

Combine the per-`(k, r)` ENNReal bounds with the bad-event decomposition to
show `μ{¬ apssvBlockBound η C} < 1` for some `C` (a real-arithmetic series
summation); then derive `μ{apssvBlockBound η C} > 0` via
`apssv_blockBound_pos_of_compl_lt_one`. -/

/-- **Auxiliary for `apssv_exists_eta_with_block_bound`**: there exists `C > 0`
such that the bad-event measure is `< 1`. This isolates the substantial
*summation argument* from the structural reduction.

**Core composition**:

1. **Bound**: `apssv_blockBound_compl_measure_le_tsum_kr` reduces
   `μ(bad)` to `∑'_k ∑'_r μ{1 ≤ k ∧ ∃ P, ‖B‖ > τ(C, k, r)}`.

2. **Per-`(k, r)` closed-form bound**: `apssv_per_kr_measure_le_regime_split`
   (or, equivalently, the M=2 / linear `_explicit` variants individually) gives
   $$ \mu(\text{per-}(k, r)) \le \mathrm{ENNReal.ofReal}
       \min\Big(\underbrace{(8\pi k/\tau + 4) \cdot 4 \cdot
       \exp(-(\tau/2)^2 / (16 \cdot 2^r))}_{\text{M}=2},
       \underbrace{(8\pi k/\tau + 4) \cdot 4 \cdot
       \exp(-(\tau/2)^2 \cdot 2^r / (64 \pi^2 k^2))}_{\text{linear}}\Big). $$
   Both arguments of `min` are *fully closed-form in `(k, r, τ)`* — the residue
   depth `h` has been internalized via `apssv_exists_h_residue_shift_strong`,
   which gives `2^h ≤ 8π·k/τ + 4`.

3. **Regime split**: substitute
   `τ(C, k, r) = C · √(r + b) · min(2^{r/2}, 2^{b - r/2})`,
   `b := apssvB k`, and evaluate `min` per regime:
   * **Short** `r ≤ b`: `min = 2^{r/2}`, so `τ² = C²(r+b)·2^r`. M=2 exp gives
     `exp(-C²(r+b)/64)`. Linear exp argument
     `(τ/2)²·2^r/(64π²k²) = C²(r+b)·2^{2r}/(256π²k²)` shrinks for `r → 0` —
     M=2 wins here.
   * **Long** `r > b`: `min = 2^{b-r/2}`, so `τ² = C²(r+b)·2^{2b-r}`. Linear
     exp `(τ/2)²·2^r/(64π²k²) = C²(r+b)·2^{2b}/(256π²k²) ≥ C²(r+b)/(64π²)`
     (using `2^b ≥ 2k`). M=2 exp arg `(τ/2)²/(16·2^r) = C²(r+b)·2^{2b-2r}/64`
     shrinks for `r → ∞` — linear wins here.

4. **Sum the exp tails** (per regime, after the prefactor `(8πk/τ + 4)` is
   absorbed into a polynomial-in-`(k, r)` factor):
   * Short: `∑_{k≥1} ∑_{r ≤ b(k)} O(poly(k, r))·exp(-C²(r+b)/64) =
     ∑_b O(2^b)·exp(-C²·b/64)·∑_{r=0}^{b} O(...) ·exp(-C²·r/64)`. For
     `C² > 128 log 2`, both sums are geometric and summable.
   * Long: `∑_{k≥1} ∑_{r > b(k)} O(poly(k, r))·exp(-C²(r+b)/(64π²))`. Similar
     geometric structure.

5. **Pick `C₀` large**: ensure total `< 1`. Concretely, `C₀ ≥ 1000` suffices
   with generous margin; a tighter analysis would give `C₀ ≈ 100`.

**Available closed-form helpers** (all proved):
* `apssv_blockBound_compl_measure_le_tsum_kr`
* `apssv_exists_h_residue_shift_strong` (with `2^h ≤ 8π·k/τ + 4`)
* `apssv_per_kr_measure_le_M2_explicit` / `_linear_explicit` (no existential)
* `apssv_per_kr_measure_le_regime_split` (min of M=2 and linear)
* `apssv_per_kr_measure_eq_zero_of_trivial` (deterministic ‖B‖ ≤ 2^r shortcut)

The remaining work is the real-arithmetic series-summation step — heavy in
constants and case analysis, modulo the deferred sub-Gaussian sorries
(`apssvBlockSum_subGaussian_tail_M2/linear`) used by the explicit helpers.

**Proof strategy used here** (non-constructive existence via measure-continuity from
above on the truncated bad event).

Define the *truncated bad event*
`badN η C N := ∃ k ≤ N, k ≥ 1 ∧ ∃ P ≤ N, ∃ r ≤ N,
  ‖B_{P,r}(k)‖ > τ(C, k, r)`.
Its measure is, by basic union/finiteness, bounded by a *finite* sum (over
`k, P, r ≤ N`) of per-`(k, P, r)` measures, each of which goes to `0` as
`C → ∞` (by the explicit M=2 / linear sub-Gaussian bounds — `τ` grows linearly
in `C`, so the exp-tail vanishes). Hence for each fixed `N`, there exists `C_N`
with `μ(badN η C_N N) < 1/2` say.

For unbounded `N`, the bad event is the *increasing* limit of `badN`; but
crucially this monotone limit need NOT have measure `0` (it can be the full
probability event for ill-behaved `η`). So the elementary Tendsto-from-above
argument *does not* directly give the conclusion.

The actual argument *does* require the genuine sub-Gaussian summation: bound
`μ{¬ apssvBlockBound η C} ≤ ∑'_{k,r} μ_per(C, k, r)` and choose `C` large
enough that the (now `(k, r)`-summable) RHS is `< 1`. This is what the proof
below carries out, leveraging the regime-split bound.

The proof factors the residual real-analysis claim into
`apssv_regime_split_tsum_lt_one`, which is closed via Tannery's dominated
convergence on the regime-split envelope at the explicit witness `C₀ = 100`. -/
@[category API, AMS 11]
lemma apssv_exists_C_with_bad_event_lt_one :
    ∃ C : ℝ, 0 < C ∧
      apssvEtaMeasure {η : List Bool → Bool | ¬ apssvBlockBound η C} < 1 := by
  -- We exhibit some `C > 0` (left abstract for now — the real-arithmetic step
  -- selects `C` large enough to make the bound below `< 1`).
  --
  -- Structural reduction (step 1): use
  -- `apssv_blockBound_compl_measure_le_tsum_kr` to bound μ(bad) by a
  -- double tsum over `(k, r)` of per-(k, r) measures. Each per-(k, r)
  -- measure is then bounded by `apssv_per_kr_measure_le_regime_split`, which
  -- gives an explicit M=2/linear regime-split formula in `(C, k, r)`.
  --
  -- The residual numerical step is the actual real-arithmetic computation:
  -- show that for some `C > 0`, the resulting double tsum (of explicit
  -- exponentials in `C²(r + b(k))`) is `< 1`. This is a heavy
  -- constants-and-cases computation; see the docstring above for the
  -- per-regime bookkeeping.
  --
  -- We package the structural reduction in full; the numerical-bound step
  -- is delegated to `apssv_regime_split_tsum_lt_one`. For each `C > 0`,
  --
  --   μ{bad C} ≤ ∑'_k ∑'_r μ_per(C, k, r)                      (step 1)
  --           ≤ ∑'_k ∑'_r ENNReal.ofReal (regime_split C k r)   (step 2)
  --
  -- and the residual claim is: ∃ C > 0, the RHS is `< 1`.
  suffices h : ∃ C : ℝ, 0 < C ∧
      ∑' k : ℕ, ∑' r : ℕ,
        apssvEtaMeasure {η : List Bool → Bool | 1 ≤ k ∧ ∃ P : ℕ,
          C * Real.sqrt ((r : ℝ) + apssvB k) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) <
          ‖apssvBlockSum η P r k‖} < 1 by
    obtain ⟨C, hC_pos, h_tsum_lt⟩ := h
    refine ⟨C, hC_pos, ?_⟩
    exact lt_of_le_of_lt (apssv_blockBound_compl_measure_le_tsum_kr C) h_tsum_lt
  -- Step 2: bound each per-(k, r) measure by ENNReal.ofReal of the
  -- regime-split closed form (encapsulated as `apssvRegimeSplitBoundReal`,
  -- which is 0 for `k = 0`).  Suffices to find `C > 0` such that the
  -- corresponding double tsum of regime-split bounds is `< 1`.
  suffices h : ∃ C : ℝ, 0 < C ∧
      ∑' k : ℕ, ∑' r : ℕ,
        ENNReal.ofReal (apssvRegimeSplitBoundReal C k r) < 1 by
    obtain ⟨C, hC_pos, h_tsum_lt⟩ := h
    refine ⟨C, hC_pos, lt_of_le_of_lt ?_ h_tsum_lt⟩
    -- Termwise bound by regime_split.
    refine ENNReal.tsum_le_tsum fun k => ?_
    refine ENNReal.tsum_le_tsum fun r => ?_
    by_cases hk : 1 ≤ k
    · -- Apply regime split for k ≥ 1.
      have hτ : 0 < C * Real.sqrt ((r : ℝ) + apssvB k) *
          min ((2 : ℝ) ^ ((r : ℝ) / 2))
            ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) :=
        apssv_threshold_pos C hC_pos k r hk
      have h_def : apssvRegimeSplitBoundReal C k r =
          min
            ((8 * Real.pi * (k : ℝ) /
                (C * Real.sqrt ((r : ℝ) + apssvB k) *
                  min ((2 : ℝ) ^ ((r : ℝ) / 2))
                    ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
              (4 * Real.exp
                (-(C * Real.sqrt ((r : ℝ) + apssvB k) *
                    min ((2 : ℝ) ^ ((r : ℝ) / 2))
                      ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 /
                  (16 * (2 : ℝ) ^ r))))
            ((8 * Real.pi * (k : ℝ) /
                (C * Real.sqrt ((r : ℝ) + apssvB k) *
                  min ((2 : ℝ) ^ ((r : ℝ) / 2))
                    ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2))) + 4) *
              (4 * Real.exp
                (-((C * Real.sqrt ((r : ℝ) + apssvB k) *
                    min ((2 : ℝ) ^ ((r : ℝ) / 2))
                      ((2 : ℝ) ^ ((apssvB k : ℝ) - (r : ℝ) / 2)) / 2) ^ 2 *
                  (2 : ℝ) ^ r) /
                  (64 * Real.pi ^ 2 * (k : ℝ) ^ 2)))) := by
        unfold apssvRegimeSplitBoundReal
        rw [dif_pos ⟨hk, hC_pos⟩]
      rw [h_def]
      exact apssv_per_kr_measure_le_regime_split k r hk _ hτ
    · -- For k = 0, the LHS is `μ ∅ = 0`; the RHS is `ENNReal.ofReal 0 = 0`.
      have hk0 : k = 0 := by omega
      subst hk0
      have h_empty : {η : List Bool → Bool | 1 ≤ (0 : ℕ) ∧ ∃ P : ℕ,
          C * Real.sqrt ((r : ℝ) + apssvB 0) *
            min ((2 : ℝ) ^ ((r : ℝ) / 2))
              ((2 : ℝ) ^ ((apssvB 0 : ℝ) - (r : ℝ) / 2)) <
          ‖apssvBlockSum η P r 0‖} = ∅ := by
        ext η; simp
      rw [h_empty, MeasureTheory.measure_empty]
      exact zero_le _
  -- The remaining residual numerical step: choose `C > 0` such that the
  -- explicit double tsum of `min(M=2, linear)` real bounds is `< 1`.
  --
  -- Sketch (per-regime estimation):
  -- Substitute `τ := C·√(r+b(k))·min(2^{r/2}, 2^{b-r/2})`.
  -- * Short regime `r ≤ b(k)`: `min = 2^{r/2}`, M=2 exp arg `= -C²(r+b)/64`.
  -- * Long regime `r > b(k)`: `min = 2^{b-r/2}`, linear exp arg
  --   `= -(τ/2)²·2^r/(64π²k²) = -C²(r+b)·2^{2b}/(256π²k²) ≤ -C²(r+b)/(64π²)`,
  --   using `2^b ≥ 2k` from `apssvB`.
  -- Both regimes give an exponential `exp(-c·C²·(r+b))`, and the prefactor
  -- `(8πk/τ + 4)·4` is a polynomial-in-(k, r) factor. The double tsum is
  -- dominated by a geometric series in `(r, b(k))`, summable for `C` large.
  -- Picking `C` large enough drives the total below `1`.
  --
  -- Numerical claim:
  --   ∃ C > 0, ∑' k r, ENNReal.ofReal (apssvRegimeSplitBoundReal C k r) < 1.
  -- This is `apssv_regime_split_tsum_lt_one`.
  exact apssv_regime_split_tsum_lt_one

/-- **Union bound to existence (Step 7 of [APSSV26b Prop 3.5])**: there exists a
constant `C₀ > 0` such that the random `η` satisfies `apssvBlockBound η C₀` with
positive probability — in particular, the bad-event measure is `< 1`.

**Proof structure**: define for each `(k, P, r)` with `k ≥ 1` the bad event
$$ E_{k, P, r} := \{\eta : \|B_{P, r}(k)\| >
   C_0 \cdot \sqrt{r + b(k)} \cdot \min(2^{r/2}, 2^{b(k) - r/2}) \}. $$
For $C_0$ large enough we want the total probability of $\bigcup E_{k,P,r}$ to
be `< 1`.

**Status**: closed. The proof composes the substantial structural infrastructure:

1. **Variance**: closed in three forms via `apssvBlockSum_variance_eq` (the
   formula `∫ ‖B‖² = 2^r·(1 - ‖α‖²)`), `apssvBlockSum_variance_bound` (`≤ 2·2^r`),
   `apssvBlockSum_variance_bound_short` (`≤ 2·2^(2b-r)` for `r ≤ b`), and
   `apssvBlockSum_variance_bound_long` (`≤ 4π·k`, derived from the Step 2
   linear Fourier-coefficient bound `‖1 - α‖ ≤ 2π·k/2^r`).

2. **Universal-`P` reduction**: closed via Lemma 3.6 (`apssvT_residue_diff_bound`,
   `apssvBlockSum_residue_diff_bound`) and the `apssvBlockSum_residue_union_bound`
   transformation, which converts `{η | ∃ P, ‖B_P‖ > τ}` into a finite union
   over `Q ∈ {0, ..., 2^h - 1}` for any reduction depth `h` with
   `2π·k/2^h ≤ τ/2`.

3. **Trivial-bound shortcut**: `apssvBlockSum_bad_event_eq_empty_of_two_pow_le`
   handles the small-`r` regime where `τ ≥ 2^r ≥ ‖B‖`.

4. **Centered decomposition** (`B = ∑_w Z_w`): the unified identity
   `apssvBlockSum_eq_centered_sum` states `B = ∑_w c_w · (Y_w - α)` for any
   `k ≥ 1`. The bias term `α · J_sum` vanishes identically by
   `apssv_alpha_J_sum_eq_zero` (case-split: `1 ≤ k % 2^r` ⟹ `J_sum = 0` by
   the deterministic root-of-unity cancellation `apssv_j_sum_eq_zero`;
   `2^r ∣ k` ⟹ `α = 0` by bit-flip symmetry). The summands satisfy
   `‖Z_w‖ ≤ 4π·k/2^r` (`apssvBlockSum_centered_summand_norm_bound`).

The **exponential / sub-Gaussian sharpening** uses Mathlib's
`Kernel.HasSubgaussianMGF` chassis (real-valued — split `B` into `Re B + i·Im B`
and apply Hoeffding componentwise). Conditional on `F_{<r}`, the `c_w` are
constants (short-prefix-measurable) and the `(Y_w)_w` are independent (disjoint
long-prefix coordinates), so the `(Z_w)_w` are conditionally independent and
bounded by `4π·k/2^r`. Hoeffding yields
`μ{‖B‖ > t} ≤ 4 exp(-t²·2^r/(64π²·k²))` — exponentially summable across
`(k, r)`, with residue-reduction shrinkage absorbing the `P`-quantifier. The
final summation is `apssv_regime_split_tsum_lt_one` (Tannery + envelope at
explicit witness `C₀ = 100`). -/
@[category API, AMS 11]
lemma apssv_exists_eta_with_block_bound :
    ∃ C : ℝ, 0 < C ∧
      0 < apssvEtaMeasure {η | apssvBlockBound η C} := by
  obtain ⟨C₀, hC₀_pos, h_bad_lt⟩ := apssv_exists_C_with_bad_event_lt_one
  refine ⟨C₀, hC₀_pos, ?_⟩
  exact apssv_blockBound_pos_of_compl_lt_one
    (apssvBlockBound_measurableSet C₀) h_bad_lt

/-- The event `{η | apssvX η j = 0}` is the set of `η` whose values match every digit
of `j` exactly: `η (apssvPrefix j i) = j.testBit i` for all `i`.

A nonneg tsum equals zero iff every term is zero; the `i`-th summand is zero iff
the `xor` is `false`, i.e. iff `η (apssvPrefix j i) = j.testBit i`. -/
@[category API, AMS 11]
lemma apssvX_eq_zero_iff (η : List Bool → Bool) (j : ℕ) :
    apssvX η j = 0 ↔ ∀ i : ℕ, η (apssvPrefix j i) = j.testBit i := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · -- Each summand is bounded by the tsum (which is 0); each summand is nonneg;
    -- so summand i = 0; then the if-clause must be false → xor false → η matches.
    have h_le : (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) /
        2 ^ (i + 1) ≤ apssvX η j :=
      Summable.le_tsum (apssvX_summable η j) i (fun k _ => apssvX_summand_nonneg η j k)
    have h_nn := apssvX_summand_nonneg η j i
    have h_eq_zero : (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) /
        2 ^ (i + 1) = 0 := le_antisymm (h_le.trans h.le) h_nn
    have h2pow_pos : (0 : ℝ) < 2^(i+1) := by positivity
    rw [div_eq_zero_iff] at h_eq_zero
    rcases h_eq_zero with hxor_false | hpow_zero
    · by_contra hne
      have h_xor_true : (j.testBit i).xor (η (apssvPrefix j i)) = true := by
        cases hb : j.testBit i <;> cases he : η (apssvPrefix j i) <;> simp_all
      rw [h_xor_true] at hxor_false
      simp at hxor_false
    · exact absurd hpow_zero h2pow_pos.ne'
  · -- All summands are 0 → tsum is 0.
    have h_zero : ∀ i,
        (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) /
          2 ^ (i + 1) = 0 := by
      intro i
      have h_xor_false : (j.testBit i).xor (η (apssvPrefix j i)) = false := by
        rw [h i]; cases j.testBit i <;> rfl
      rw [h_xor_false]; simp
    unfold apssvX
    rw [tsum_congr h_zero, tsum_zero]

/-- **Coordinate-match null**: For any target `f₀ : ℕ → Bool`, the event that
`η (apssvPrefix j i) = f₀ i` for *all* `i : ℕ` simultaneously has probability `0`.

**Proof**: the event is the preimage under `φ η i := η (apssvPrefix j i)` of the
singleton `{f₀} ⊆ (ℕ → Bool)`. The prefixes are pairwise distinct (different
lengths, by `apssvPrefix_injective`), so by `apssv_eta_iIndepFun.precomp` and
`iIndepFun_iff_map_fun_eq_infinitePi_map`, the pushforward `φ_*μ` is the infinite
product `infinitePi (fun _ : ℕ => apssvBoolMeasure)`. By `infinitePi_singleton`
this is `∏' i, 1/2`, and the infinite product `∏' i : ℕ, (1/2 : ℝ≥0∞) = 0`
(via `ENNReal.tprod_eq_iInf_prod` and `(1/2)^n → 0`). -/
@[category API, AMS 11]
lemma apssv_eta_match_null (j : ℕ) (f₀ : ℕ → Bool) :
    apssvEtaMeasure {η | ∀ i : ℕ, η (apssvPrefix j i) = f₀ i} = 0 := by
  -- Setup the projection η ↦ (η (apssvPrefix j ·)).
  set φ : (List Bool → Bool) → (ℕ → Bool) := fun η i => η (apssvPrefix j i)
  have h_meas_φ : Measurable φ :=
    measurable_pi_lambda _ (fun i => apssv_eta_coord_measurable _)
  -- The set is φ ⁻¹' {f₀}.
  have h_set_pre : {η : List Bool → Bool | ∀ i : ℕ, η (apssvPrefix j i) = f₀ i} =
      φ ⁻¹' {f₀} := by
    ext η
    refine ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [h_set_pre]
  rw [← MeasureTheory.Measure.map_apply h_meas_φ (MeasurableSet.singleton f₀)]
  -- The pushforward is infinitePi.
  have h_meas_each : ∀ i : ℕ, Measurable (fun η : List Bool → Bool => η (apssvPrefix j i)) :=
    fun i => apssv_eta_coord_measurable _
  have h_iIndep : ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (η : List Bool → Bool) => η (apssvPrefix j i)) apssvEtaMeasure :=
    apssv_eta_iIndepFun.precomp (apssvPrefix_injective j)
  have h_each_law : ∀ i : ℕ,
      apssvEtaMeasure.map (fun η : List Bool → Bool => η (apssvPrefix j i)) = apssvBoolMeasure :=
    fun i => apssv_eta_coord_law _
  have h_pushforward :
      apssvEtaMeasure.map φ = MeasureTheory.Measure.infinitePi (fun _ : ℕ => apssvBoolMeasure) := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map h_meas_each).mp h_iIndep
    rw [h]
    congr 1
    funext i
    exact h_each_law i
  rw [h_pushforward, MeasureTheory.Measure.infinitePi_singleton]
  -- ∏' i, apssvBoolMeasure {f₀ i} = ∏' i, 1/2 = 0.
  have h_each : ∀ i : ℕ, apssvBoolMeasure {f₀ i} = (1/2 : ENNReal) :=
    fun i => apssvBoolMeasure_singleton (f₀ i)
  rw [tprod_congr h_each]
  -- ∏' i : ℕ, (1/2 : ENNReal) = 0.
  rw [ENNReal.tprod_eq_iInf_prod (fun _ => by norm_num : ∀ _ : ℕ, (1/2 : ENNReal) ≤ 1)]
  refine le_antisymm ?_ (zero_le _)
  -- For each n, the iInf ≤ ∏ over Finset.range n = (1/2)^n.
  have h_le_pow : ∀ n : ℕ, (⨅ s : Finset ℕ, ∏ _ ∈ s, (1/2 : ENNReal)) ≤ (1/2 : ENNReal)^n := by
    intro n
    refine iInf_le_of_le (Finset.range n) ?_
    rw [Finset.prod_const, Finset.card_range]
  have h_anti : Antitone (fun n : ℕ => (1/2 : ENNReal)^n) := fun n m hnm =>
    pow_le_pow_right_of_le_one' (by norm_num) hnm
  have h_tendsto : Filter.Tendsto (fun n : ℕ => (1/2 : ENNReal)^n) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have h_iInf_eq : ⨅ n : ℕ, (1/2 : ENNReal)^n = 0 := iInf_eq_of_tendsto h_anti h_tendsto
  calc (⨅ s : Finset ℕ, ∏ _ ∈ s, (1/2 : ENNReal))
      ≤ ⨅ n : ℕ, (1/2 : ENNReal)^n := le_iInf h_le_pow
    _ = 0 := h_iInf_eq

/-- The event `{η | apssvX η j = 1}` is the set of `η` whose values *anti*-match
every digit of `j`: `η (apssvPrefix j i) = !(j.testBit i)` for all `i`.

The maximum tsum value is `1` (since each summand `≤ (1/2)^(i+1)` and
`∑ (1/2)^(i+1) = 1`); equality requires every summand to attain its maximum,
i.e. the `xor` to be `true` for every `i`, which means `η ≠ j.testBit i`. -/
@[category API, AMS 11]
lemma apssvX_eq_one_iff (η : List Bool → Bool) (j : ℕ) :
    apssvX η j = 1 ↔ ∀ i : ℕ, η (apssvPrefix j i) = ! (j.testBit i) := by
  -- The geometric envelope: ∑' i, (1/2)^(i+1) = 1.
  have h_geom_summable : Summable (fun i : ℕ => ((1 / 2 : ℝ)) ^ (i + 1)) := by
    have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact h.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
  have h_geom_tsum : ∑' i : ℕ, ((1 / 2 : ℝ)) ^ (i + 1) = 1 := by
    simp_rw [show ∀ i : ℕ, ((1 / 2 : ℝ)) ^ (i + 1) = (1/2) * (1/2)^i from fun i => by
      rw [pow_succ]; ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · -- Forward: by contradiction, suppose η i₀ matches j.testBit i₀, then summand i₀ < max.
    by_contra hne
    have h_xor_false : (j.testBit i).xor (η (apssvPrefix j i)) = false := by
      cases hb : j.testBit i <;> cases he : η (apssvPrefix j i) <;> simp_all
    have h_summand_zero :
        (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) / 2 ^ (i + 1) = 0 := by
      rw [h_xor_false]; simp
    have h_max_pos : (0 : ℝ) < ((1 / 2 : ℝ)) ^ (i + 1) := by positivity
    have h_strict :
        (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) / 2 ^ (i + 1) <
        ((1 / 2 : ℝ)) ^ (i + 1) := by rw [h_summand_zero]; exact h_max_pos
    have h_strict_tsum :
        ∑' i, (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)
          < ∑' i : ℕ, ((1 / 2 : ℝ)) ^ (i + 1) :=
      Summable.tsum_lt_tsum (apssvX_summand_le η j) h_strict (apssvX_summable η j)
        h_geom_summable
    rw [h_geom_tsum] at h_strict_tsum
    have h_lt : apssvX η j < 1 := h_strict_tsum
    linarith
  · -- Backward: each summand = (1/2)^(i+1), tsum = ∑ (1/2)^(i+1) = 1.
    have h_summand_eq : ∀ i,
        (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) / 2 ^ (i + 1) =
        ((1 / 2 : ℝ)) ^ (i + 1) := by
      intro i
      have h_xor_true : (j.testBit i).xor (η (apssvPrefix j i)) = true := by
        rw [h i]; cases j.testBit i <;> rfl
      rw [h_xor_true]
      simp only [if_true, one_div]
      rw [inv_pow]
    unfold apssvX
    rw [tsum_congr h_summand_eq, h_geom_tsum]

/-- **Single-event null at zero**: `μ{η | apssvX η j = 0} = 0`. -/
@[category API, AMS 11]
lemma apssvX_eq_zero_event_null (j : ℕ) :
    apssvEtaMeasure {η | apssvX η j = 0} = 0 := by
  rw [show {η : List Bool → Bool | apssvX η j = 0} =
      {η | ∀ i : ℕ, η (apssvPrefix j i) = (fun i => j.testBit i) i} from by
    ext η; exact apssvX_eq_zero_iff η j]
  exact apssv_eta_match_null j (fun i => j.testBit i)

/-- **Single-event null at one**: `μ{η | apssvX η j = 1} = 0`. -/
@[category API, AMS 11]
lemma apssvX_eq_one_event_null (j : ℕ) :
    apssvEtaMeasure {η | apssvX η j = 1} = 0 := by
  rw [show {η : List Bool → Bool | apssvX η j = 1} =
      {η | ∀ i : ℕ, η (apssvPrefix j i) = (fun i => ! (j.testBit i)) i} from by
    ext η; exact apssvX_eq_one_iff η j]
  exact apssv_eta_match_null j (fun i => ! (j.testBit i))

/-- **Boundary almost-everywhere fact**: under the random `η`, almost surely
`apssvX η j ∈ (0, 1)` for all `j` simultaneously.

The complement event `∃ j, apssvX η j ∈ {0, 1}` is contained in the countable
union `⋃_j ({η | apssvX η j = 0} ∪ {η | apssvX η j = 1})`. Each constituent
event has measure zero (`apssvX_eq_zero_event_null`, `apssvX_eq_one_event_null`),
so the union has measure zero. -/
@[category API, AMS 11]
lemma apssv_boundary_ae :
    ∀ᵐ η ∂apssvEtaMeasure, ∀ j : ℕ, apssvX η j ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [MeasureTheory.ae_iff]
  -- {η | ¬ ∀ j, apssvX η j ∈ Ioo 0 1} ⊆ ⋃ j, ({apssvX η j = 0} ∪ {apssvX η j = 1}).
  set U : Set (List Bool → Bool) :=
    ⋃ j : ℕ, ({η | apssvX η j = 0} ∪ {η | apssvX η j = 1})
  have h_subset : {η | ¬ ∀ j : ℕ, apssvX η j ∈ Set.Ioo (0 : ℝ) 1} ⊆ U := by
    intro η hη
    push_neg at hη
    obtain ⟨j, hj⟩ := hη
    have h_nn := apssvX_nonneg η j
    have h_le := apssvX_le_one η j
    rw [Set.mem_iUnion]
    refine ⟨j, ?_⟩
    rcases lt_or_eq_of_le h_nn with h0_lt | h0_eq
    · rcases lt_or_eq_of_le h_le with h1_lt | h1_eq
      · exact absurd ⟨h0_lt, h1_lt⟩ hj
      · exact Or.inr h1_eq
    · exact Or.inl h0_eq.symm
  refine MeasureTheory.measure_mono_null h_subset ?_
  -- The countable union has measure 0.
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro j
  rw [MeasureTheory.measure_union_null_iff]
  exact ⟨apssvX_eq_zero_event_null j, apssvX_eq_one_event_null j⟩

/-- The "alternating" scrambling: `η_u = true` iff `|u|` is odd.

This deterministic `η` satisfies the boundary condition `apssvX η j ∈ (0, 1)` for all `j`:
* `apssvX η j > 0`: pick any odd `i` with `i ≥ Nat.size j`. Then `j.testBit i = false`,
  so the `i`-th summand is `(false xor true) ? 1/2^(i+1) : 0 = 1/2^(i+1) > 0`.
* `apssvX η j < 1`: pick any even `i` with `i ≥ Nat.size j`. The summand is `0`, so
  it contributes strictly less than its maximum `1/2^(i+1)`, and the total is `< 1`.

This handles only the *boundary* part of `apssv_exists_block_bound`. The block bound
must be obtained separately (probabilistically). -/
@[category API, AMS 11]
lemma apssv_alternating_boundary :
    ∀ j : ℕ, apssvX (fun u => decide (u.length % 2 = 1)) j ∈ Set.Ioo (0 : ℝ) 1 := by
  intro j
  let η : List Bool → Bool := fun u => decide (u.length % 2 = 1)
  -- η at prefix of length i = (i is odd).
  have h_prefix_len : ∀ i : ℕ, (apssvPrefix j i).length = i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [apssvPrefix_succ, List.length_append, ih]; simp
  have h_eta_at : ∀ i : ℕ, η (apssvPrefix j i) = decide (i % 2 = 1) := by
    intro i
    show decide ((apssvPrefix j i).length % 2 = 1) = decide (i % 2 = 1)
    rw [h_prefix_len]
  -- Pick i_odd ≥ Nat.size j with i_odd odd, and i_even ≥ Nat.size j with i_even even.
  let N := Nat.size j
  let i_odd : ℕ := 2 * N + 1   -- ≥ N, odd
  let i_even : ℕ := 2 * N + 2  -- ≥ N, even
  have h_iodd_ge : N ≤ i_odd := by show N ≤ 2 * N + 1; omega
  have h_ieven_ge : N ≤ i_even := by show N ≤ 2 * N + 2; omega
  have h_iodd_odd : i_odd % 2 = 1 := by show (2 * N + 1) % 2 = 1; omega
  have h_ieven_even : i_even % 2 = 0 := by show (2 * N + 2) % 2 = 0; omega
  -- For i ≥ N = Nat.size j, j.testBit i = false.
  have h_j_lt : j < 2 ^ N := Nat.lt_size_self j
  have h_test_iodd : j.testBit i_odd = false :=
    Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le h_j_lt (Nat.pow_le_pow_right (by norm_num) h_iodd_ge))
  have h_test_ieven : j.testBit i_even = false :=
    Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le h_j_lt (Nat.pow_le_pow_right (by norm_num) h_ieven_ge))
  have h_eta_iodd : η (apssvPrefix j i_odd) = true := by
    rw [h_eta_at]; simpa using h_iodd_odd
  have h_eta_ieven : η (apssvPrefix j i_even) = false := by
    rw [h_eta_at]; simp; omega
  -- Define summand.
  let f : ℕ → ℝ := fun i =>
    (if (j.testBit i).xor (η (apssvPrefix j i)) then (1 : ℝ) else 0) / 2 ^ (i + 1)
  have hf_summable : Summable f := apssvX_summable η j
  have hf_nn : ∀ i, 0 ≤ f i := apssvX_summand_nonneg η j
  have h_apssvX_eq : apssvX η j = ∑' i, f i := rfl
  have hf_iodd_pos : 0 < f i_odd := by
    show 0 < (if (j.testBit i_odd).xor (η (apssvPrefix j i_odd)) then (1 : ℝ) else 0) /
         2 ^ (i_odd + 1)
    rw [h_test_iodd, h_eta_iodd]
    simp only [Bool.false_xor, if_true]
    positivity
  have hf_ieven_zero : f i_even = 0 := by
    show (if (j.testBit i_even).xor (η (apssvPrefix j i_even)) then (1 : ℝ) else 0) /
         2 ^ (i_even + 1) = 0
    rw [h_test_ieven, h_eta_ieven]; simp
  refine ⟨?_, ?_⟩
  · -- 0 < apssvX η j: extract f i_odd > 0 from the sum.
    rw [h_apssvX_eq]
    have h := hf_summable.sum_le_tsum {i_odd} (fun i _ => hf_nn i)
    simp only [Finset.sum_singleton] at h
    linarith
  · -- apssvX η j < 1: f i_even = 0 < (1/2)^(i_even+1), so sum < ∑ (1/2)^(i+1) = 1.
    have h_bound_max : ∀ i, f i ≤ ((1 : ℝ) / 2) ^ (i + 1) := apssvX_summand_le η j
    have h_geom_summable : Summable (fun i : ℕ => ((1 / 2 : ℝ)) ^ (i + 1)) := by
      have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
      exact h.mul_left (1 / 2) |>.congr (fun i => by rw [pow_succ]; ring)
    have h_geom_tsum : ∑' i : ℕ, ((1 / 2 : ℝ)) ^ (i + 1) = 1 := by
      simp_rw [show ∀ i : ℕ, ((1 / 2 : ℝ)) ^ (i + 1) = (1/2) * (1/2)^i from fun i => by
        rw [pow_succ]; ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [h_apssvX_eq, ← h_geom_tsum]
    apply Summable.tsum_lt_tsum (i := i_even) h_bound_max ?_ hf_summable h_geom_summable
    rw [hf_ieven_zero]; positivity


/-- **Existence of $\eta$ satisfying the block bound and giving values in $(0, 1)$**.

[APSSV26b Proposition 3.5] proves a probabilistic existence: i.i.d. random Bernoulli choices
for $\eta$ satisfy `apssvBlockBound η C` with positive probability. We also need
$\mathrm{apssvX}\,\eta\,j \in (0, 1)$ for all $j$ (to fit the formal statement of Erdős
problem 987 which uses `Ioo 0 1`). Both conditions hold simultaneously with positive
probability under the random construction (the boundary set has measure zero).

**Proof sketch.** Treat $\eta(u)$ as i.i.d. Bernoulli(1/2) random variables.
On each dyadic block, $B_{P,r}(k) = \sum_{w \in \{0,1\}^r} e(k \cdot (j_r(w) + T_{w,P}) / 2^r)$.
The bijection $w \mapsto j_r(w)$ (Lemma 3.3) reorganizes this sum: conditioning on the
$\eta$-values at prefixes of length $\le r-1$ (and on $T_{w,P}$, which depends only on
$\eta$-values on the *long* prefixes specific to $P$), the inner sum
$\sum_w e(k \cdot j_r(w)/2^r) \cdot e(k \cdot T_{w,P}/2^r)$ becomes a sum of conditionally
independent unit-modulus random variables: the $2^r$ summands are independent because they
correspond to disjoint sets of "long-prefix" $\eta$-values (the bits of $P$). Each summand
is *centered* — once conditioning is applied, the conditional expectation of
$e(k \cdot T_{w,P}/2^r)$ over the long-prefix randomness is zero whenever
$k \cdot 2^{-r}$ is not an integer (which holds for $r > b$, since $b \ge \log_2 k$).
Hoeffding's inequality applied to the centered sum gives sub-Gaussian tails with proxy
proportional to $2^r$, yielding the $\sqrt{r+b} \cdot \min\{2^{r/2}, 2^{b-r/2}\}$ envelope.

The countable union over the relevant parameter family $(k, P, r)$ is controlled by the
*tail summability* of the bad-event probabilities: for any fixed $r$, the conditional
independence across $P$ together with the geometric decay of failure-probabilities in
$r+b$ keeps the total measure of failure bounded.

For each $j$, the events $\mathrm{apssvX}\,\eta\,j = 0$ and $\mathrm{apssvX}\,\eta\,j = 1$
each occur with probability $0$ (each requires a specific infinite sequence of $\eta$ values).
The countable union is still measure $0$, so
$\mathbb{P}(\mathrm{apssvX}\,\eta\,j \in (0,1)\, \forall j) = 1$ — see
`apssv_alternating_boundary` for an explicit deterministic $\eta$ satisfying just the
boundary part. Combining with the positive-probability block-bound event yields a
deterministic $\eta$ with both properties.

**Status**: closed. The proof composes two probabilistic ingredients:
* the block-bound event has positive probability (`apssv_exists_eta_with_block_bound`),
* the boundary event `{η | ∀ j, apssvX η j ∈ Ioo 0 1}` has full probability
  (`apssv_boundary_ae`).
Intersecting yields a positive-measure set, hence nonempty, providing a deterministic
`η` with both properties. -/
@[category API, AMS 11]
lemma apssv_exists_block_bound :
    ∃ (η : List Bool → Bool) (C : ℝ), 0 < C ∧ apssvBlockBound η C ∧
      ∀ j : ℕ, apssvX η j ∈ Set.Ioo (0 : ℝ) 1 := by
  -- Combine the two probabilistic ingredients: the block-bound event has positive measure
  -- (apssv_exists_eta_with_block_bound), the boundary event has full probability
  -- (apssv_boundary_ae); intersected they have positive measure, hence nonempty.
  obtain ⟨C, hC_pos, hC_meas⟩ := apssv_exists_eta_with_block_bound
  set A : Set (List Bool → Bool) := {η | apssvBlockBound η C}
  set B : Set (List Bool → Bool) := {η | ∀ j : ℕ, apssvX η j ∈ Set.Ioo (0 : ℝ) 1}
  have hB_ae : ∀ᵐ η ∂apssvEtaMeasure, η ∈ B := apssv_boundary_ae
  have h_inter : apssvEtaMeasure (B ∩ A) = apssvEtaMeasure A :=
    apssvEtaMeasure.measure_inter_eq_of_ae hB_ae
  have h_pos : 0 < apssvEtaMeasure (B ∩ A) := by rw [h_inter]; exact hC_meas
  obtain ⟨η, hη⟩ := MeasureTheory.nonempty_of_measure_ne_zero h_pos.ne'
  exact ⟨η, C, hC_pos, hη.2, hη.1⟩

/- ## Real-analysis helpers for `apssv_partial_sum_bound` -/

/-- Conversion: `(2:ℝ)^((ρ:ℝ)/2) = (Real.sqrt 2)^ρ` for `ρ : ℕ`. Used to reduce real-exponent
power arithmetic to natural-exponent arithmetic (for `Finset.geom_sum_eq` etc.). -/
@[category API, AMS 11]
lemma apssv_two_rpow_half (ρ : ℕ) : (2 : ℝ) ^ ((ρ : ℝ) / 2) = (Real.sqrt 2) ^ ρ := by
  rw [Real.rpow_div_two_eq_sqrt (ρ : ℝ) (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.rpow_natCast _ ρ

/-- Geometric envelope short-block bound:
$\sum_{\rho=0}^{b} 2^{\rho/2} \le 4 \cdot 2^{b/2}$. The series is geometric with ratio
$\sqrt{2}$; the explicit constant `4 ≥ √2/(√2-1) ≈ 3.41` absorbs the closed form. -/
@[category API, AMS 11]
lemma apssv_geom_short (b : ℕ) :
    ∑ ρ ∈ Finset.range (b + 1), (2 : ℝ) ^ ((ρ : ℝ) / 2) ≤ 4 * (2 : ℝ) ^ ((b : ℝ) / 2) := by
  induction b with
  | zero =>
    simp [Real.rpow_zero]
  | succ b ih =>
    rw [Finset.sum_range_succ]
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h2bpos : (0 : ℝ) < (2 : ℝ) ^ ((b : ℝ) / 2) := Real.rpow_pos_of_pos h2pos _
    have h_succ_eq : (2 : ℝ) ^ ((↑(b + 1) : ℝ) / 2) =
        Real.sqrt 2 * (2 : ℝ) ^ ((b : ℝ) / 2) := by
      rw [show ((↑(b + 1) : ℝ) / 2) = (b : ℝ) / 2 + 1 / 2 by push_cast; ring]
      rw [Real.rpow_add h2pos]
      rw [show ((2 : ℝ) ^ ((1 : ℝ) / 2)) = Real.sqrt 2 from (Real.sqrt_eq_rpow 2).symm]
      ring
    rw [h_succ_eq]
    -- Need 4·√2 ≥ 4 + √2, i.e., 3√2 ≥ 4, i.e., (4/3)² ≤ 2.
    have hsqrt2_ge : (4 : ℝ) ≤ 3 * Real.sqrt 2 := by
      have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg (2 : ℝ), h2]
    nlinarith [ih, h2bpos, Real.sqrt_nonneg (2 : ℝ), hsqrt2_ge]

/-- Geometric envelope long-block bound (tail series):
$\sum_{\tau=1}^{\infty} 2^{-\tau/2} \le 4$. -/
@[category API, AMS 11]
lemma apssv_geom_tail :
    ∀ N : ℕ, ∑ τ ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ (-(τ : ℝ) / 2) ≤ 4 := by
  intro N
  -- Convert: 2^(-τ/2) = ((sqrt 2)⁻¹)^τ.
  have h_conv : ∀ τ : ℕ, (2 : ℝ) ^ (-(τ : ℝ) / 2) = ((Real.sqrt 2)⁻¹) ^ τ := by
    intro τ
    rw [show (-(τ : ℝ) / 2) = -((τ : ℝ) / 2) by ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [apssv_two_rpow_half, ← inv_pow]
  rw [Finset.sum_congr rfl (fun τ _ => h_conv τ)]
  set r : ℝ := (Real.sqrt 2)⁻¹ with hr_def
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have h_sqrt2_gt_1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hr_pos : 0 < r := inv_pos.mpr h_sqrt2_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    exact inv_lt_one_of_one_lt₀ h_sqrt2_gt_1
  -- ∑_{τ ∈ Ico 1 (N+1)} r^τ = (∑_{τ ∈ range (N+1)} r^τ) - 1.
  have h_eq : ∑ τ ∈ Finset.Ico 1 (N + 1), r ^ τ =
              (∑ τ ∈ Finset.range (N + 1), r ^ τ) - 1 := by
    have h_range_eq : Finset.range (N + 1) = insert 0 (Finset.Ico 1 (N + 1)) := by
      ext x
      simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [h_range_eq, Finset.sum_insert (by simp)]
    simp
  rw [h_eq]
  -- Bound: ∑_{τ ∈ range (N+1)} r^τ ≤ ∑'_{τ} r^τ = 1/(1-r).
  have h_summable := summable_geometric_of_lt_one hr_nn hr_lt_one
  have h_tsum := tsum_geometric_of_lt_one hr_nn hr_lt_one
  have h_partial : ∑ τ ∈ Finset.range (N + 1), r ^ τ ≤ (1 - r)⁻¹ := by
    rw [← h_tsum]
    exact h_summable.sum_le_tsum _ (fun τ _ => pow_nonneg hr_nn τ)
  -- Final: (1-r)⁻¹ - 1 ≤ 4 iff (1-r)⁻¹ ≤ 5 iff 1/5 ≤ 1 - r iff r ≤ 4/5.
  -- r = 1/√2, so 1/r = √2. Need √2 ≥ 5/4. Square: 2 ≥ 25/16. True.
  have h_one_minus_r_pos : 0 < 1 - r := by linarith
  have h_r_le_45 : r ≤ 4 / 5 := by
    rw [hr_def]
    rw [inv_le_comm₀ h_sqrt2_pos (by norm_num : (0 : ℝ) < 4 / 5)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have h_inv : (1 - r)⁻¹ ≤ 5 := by
    rw [inv_le_iff_one_le_mul₀ h_one_minus_r_pos]
    linarith
  linarith

/-- Geometric envelope long-block sum (tail with √τ factor):
$\sum_{\tau=1}^{\infty} \sqrt{\tau} \cdot 2^{-\tau/2} \le 10$. The closed form for
$\sum_{\tau \ge 1} \tau \cdot r^{\tau}$ at $r = 1/\sqrt{2}$ is $r/(1-r)^2 = 4 + 3\sqrt{2} \approx 8.24$;
bounding $\sqrt{\tau} \le \tau$ for $\tau \ge 1$ gives the constant 10 (with slack). -/
@[category API, AMS 11]
lemma apssv_geom_tail_sqrt :
    ∀ N : ℕ, ∑ τ ∈ Finset.Ico 1 (N + 1), Real.sqrt (τ : ℝ) * (2 : ℝ) ^ (-(τ : ℝ) / 2) ≤ 10 := by
  intro N
  -- Bound √τ ≤ τ for τ ≥ 1.
  have h_sqrt_le : ∀ τ ∈ Finset.Ico 1 (N + 1),
      Real.sqrt (τ : ℝ) * (2 : ℝ) ^ (-(τ : ℝ) / 2) ≤ (τ : ℝ) * (2 : ℝ) ^ (-(τ : ℝ) / 2) := by
    intro τ hτ
    rw [Finset.mem_Ico] at hτ
    have hτ_pos : (0 : ℝ) < τ := by exact_mod_cast hτ.1
    have h_sqrt_le_self : Real.sqrt (τ : ℝ) ≤ (τ : ℝ) := by
      have h1 : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ.1
      calc Real.sqrt (τ : ℝ)
          ≤ Real.sqrt ((τ : ℝ) * τ) := by
            apply Real.sqrt_le_sqrt
            nlinarith
        _ = (τ : ℝ) := by rw [Real.sqrt_mul_self hτ_pos.le]
    apply mul_le_mul_of_nonneg_right h_sqrt_le_self
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  refine le_trans (Finset.sum_le_sum h_sqrt_le) ?_
  -- Convert: τ · 2^(-τ/2) = τ · (1/√2)^τ.
  have h_conv : ∀ τ : ℕ,
      (τ : ℝ) * (2 : ℝ) ^ (-(τ : ℝ) / 2) = (τ : ℝ) * ((Real.sqrt 2)⁻¹) ^ τ := by
    intro τ
    congr 1
    rw [show (-(τ : ℝ) / 2) = -((τ : ℝ) / 2) by ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [apssv_two_rpow_half, ← inv_pow]
  rw [Finset.sum_congr rfl (fun τ _ => h_conv τ)]
  set r : ℝ := (Real.sqrt 2)⁻¹ with hr_def
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have h_sqrt2_gt_1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hr_pos : 0 < r := inv_pos.mpr h_sqrt2_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ h_sqrt2_gt_1
  have hr_norm_lt_one : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr_nn]
  -- Bound by tsum.
  have h_summable : Summable (fun τ : ℕ => (τ : ℝ) * r ^ τ) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr_norm_lt_one).summable
  have h_tsum : (∑' τ : ℕ, (τ : ℝ) * r ^ τ) = r / (1 - r) ^ 2 :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr_norm_lt_one).tsum_eq
  have h_partial_le : ∑ τ ∈ Finset.Ico 1 (N + 1), (τ : ℝ) * r ^ τ ≤ r / (1 - r) ^ 2 := by
    rw [← h_tsum]
    apply h_summable.sum_le_tsum
    intro τ _
    exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hr_nn τ)
  refine le_trans h_partial_le ?_
  -- r/(1-r)² ≤ 10. With r = 1/√2, 1-r = (√2-1)/√2, (1-r)² = (3-2√2)/2.
  -- r/(1-r)² = (1/√2)/((3-2√2)/2) = 2/(√2(3-2√2)) = 2/(3√2-4).
  -- Need 2/(3√2-4) ≤ 10, i.e., 2 ≤ 10(3√2-4) = 30√2 - 40, i.e., 42 ≤ 30√2, i.e., 7/5 ≤ √2.
  -- (7/5)² = 49/25 ≤ 2 = (√2)². ✓
  have h_one_minus_r_pos : 0 < 1 - r := by linarith
  have h_one_minus_r_sq_pos : 0 < (1 - r) ^ 2 := pow_pos h_one_minus_r_pos 2
  rw [div_le_iff₀ h_one_minus_r_sq_pos]
  -- Need: r ≤ 10 · (1-r)². With r = (√2)⁻¹ and (1-r)² = (3-2√2)/2:
  -- 10·(1-r)² = 10·(3-2√2)/2 = 5(3-2√2) = 15 - 10√2.
  -- So need (√2)⁻¹ ≤ 15 - 10√2, i.e., 1 ≤ √2(15 - 10√2) = 15√2 - 20, i.e., 21 ≤ 15√2,
  -- i.e., 7 ≤ 5√2, i.e., 49 ≤ 50. ✓
  have h_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h_sqrt_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_sqrt_le : Real.sqrt 2 ≤ 10 / 7 := by
    have h1 : Real.sqrt 2 ≤ Real.sqrt (100 / 49) := Real.sqrt_le_sqrt (by norm_num)
    rwa [show ((100 / 49 : ℝ)) = (10 / 7) ^ 2 from by norm_num,
         Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10 / 7)] at h1
  have h_sqrt_inv : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 := inv_mul_cancel₀ h_sqrt2_pos.ne'
  rw [hr_def]
  -- Multiply by √2 on both sides: √2 · (√2)⁻¹ ≤ √2 · 10 · (1 - (√2)⁻¹)²
  -- 1 ≤ 10√2·((s-1)/s)² where s = √2, i.e., 1 ≤ 10√2·(s-1)²/s² = 10·(s-1)²/√2 = 5·(s-1)²·√2
  -- (s-1)² = 3 - 2√2, so 5√2·(3-2√2) = 15√2 - 10·2 = 15√2 - 20.
  -- Need 1 ≤ 15√2 - 20, i.e., 21 ≤ 15√2, i.e., 7/5 ≤ √2. (7/5)² = 1.96 ≤ 2. ✓
  nlinarith [h_sq, h_sqrt_nn, h_sqrt2_pos, h_sqrt2_gt_1, h_sqrt_le,
    sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (5 * Real.sqrt 2 - 7),
    sq_nonneg (1 - (Real.sqrt 2)⁻¹), h_sqrt_inv]

/-- The full geometric envelope bound: for any finite range of levels, the per-block bound
is uniformly bounded by `K · √(b+1) · 2^(b/2)` (for absolute K).

Proof outline (case-split on `M ≤ b` vs `M > b`):
* **`M ≤ b` (only short blocks)**: every `ρ ∈ [0, M]` has `ρ ≤ b`, so
  `min(2^(ρ/2), 2^(b-ρ/2)) = 2^(ρ/2)`. Bound `√(ρ+b) ≤ √(2b)`, extend the sum to
  `[0, b]`, apply `apssv_geom_short`. Total `≤ 4√(2b)·2^(b/2) ≤ 4√2·√(b+1)·2^(b/2)`.
* **`M > b` (short + long blocks)**: split `[0, M] = [0, b] ⊔ [b+1, M]`.
  Short part bounded as above. Long part: substitute `τ = ρ - b`, get
  `∑_{τ=1}^{M-b} √(2b+τ) · 2^(b/2) · 2^(-τ/2)`. Bound `√(2b+τ) ≤ √(2b) + √τ`
  (sub-additivity of sqrt), apply `apssv_geom_tail` and `apssv_geom_tail_sqrt`.
  Total `≤ 8√(2b)·2^(b/2) + 10·2^(b/2) ≤ 22√(b+1)·2^(b/2)`.
The constant `40` absorbs all rounding. -/
@[category API, AMS 11]
lemma apssv_geom_envelope (b M : ℕ) :
    ∑ ρ ∈ Finset.range (M + 1),
      Real.sqrt ((ρ : ℝ) + b) *
        min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) ≤
      40 * Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2) := by
  -- Common positivity facts.
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have h_2pow_b_nn : 0 ≤ (2 : ℝ) ^ ((b : ℝ) / 2) := Real.rpow_nonneg h2_nn _
  have h_sqrt_b1_nn : 0 ≤ Real.sqrt ((b : ℝ) + 1) := Real.sqrt_nonneg _
  have h_sqrt_2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_sqrt_2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have h_sqrt_2_le_2 : Real.sqrt 2 ≤ 2 := by nlinarith [h_sqrt_2_sq, h_sqrt_2_nn]
  have h_sqrt_2b_le : Real.sqrt (2 * (b : ℝ)) ≤ Real.sqrt 2 * Real.sqrt ((b : ℝ) + 1) := by
    rw [← Real.sqrt_mul h2_nn]
    apply Real.sqrt_le_sqrt; linarith
  -- Key algebra: 4·√(2b)·2^(b/2) ≤ 40·√(b+1)·2^(b/2).
  have h_short_bound_pre : 4 * Real.sqrt (2 * (b : ℝ)) ≤ 40 * Real.sqrt ((b : ℝ) + 1) := by
    nlinarith [h_sqrt_2b_le, h_sqrt_2_le_2, h_sqrt_b1_nn, h_sqrt_2_nn]
  have h_short_bound_le_total :
      4 * Real.sqrt (2 * (b : ℝ)) * (2 : ℝ) ^ ((b : ℝ) / 2) ≤
        40 * Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right h_short_bound_pre h_2pow_b_nn
  by_cases hMb : M ≤ b
  · -- Case M ≤ b: only short blocks.
    have h_term_le : ∀ ρ ∈ Finset.range (M + 1),
        Real.sqrt ((ρ : ℝ) + b) *
          min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) ≤
        Real.sqrt (2 * (b : ℝ)) * (2 : ℝ) ^ ((ρ : ℝ) / 2) := by
      intro ρ hρ
      rw [Finset.mem_range] at hρ
      have hρ_le_b : (ρ : ℝ) ≤ b := by exact_mod_cast (show ρ ≤ b by omega)
      have h_min_eq : min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) =
                      (2 : ℝ) ^ ((ρ : ℝ) / 2) := by
        apply min_eq_left
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      rw [h_min_eq]
      apply mul_le_mul_of_nonneg_right
      · apply Real.sqrt_le_sqrt; linarith
      · exact Real.rpow_nonneg h2_nn _
    refine le_trans (Finset.sum_le_sum h_term_le) ?_
    rw [← Finset.mul_sum]
    have h_sqrt_2b_nn : 0 ≤ Real.sqrt (2 * (b : ℝ)) := Real.sqrt_nonneg _
    -- Extend range from M+1 to b+1.
    have hMb_nat : M + 1 ≤ b + 1 := by omega
    have h_subset : Finset.range (M + 1) ⊆ Finset.range (b + 1) :=
      Finset.range_subset_range.mpr hMb_nat
    have h_extend : ∑ ρ ∈ Finset.range (M + 1), (2 : ℝ) ^ ((ρ : ℝ) / 2) ≤
                    ∑ ρ ∈ Finset.range (b + 1), (2 : ℝ) ^ ((ρ : ℝ) / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg h_subset
        (fun _ _ _ => Real.rpow_nonneg h2_nn _)
    refine le_trans (mul_le_mul_of_nonneg_left h_extend h_sqrt_2b_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (apssv_geom_short b) h_sqrt_2b_nn) ?_
    -- √(2b) · (4 · 2^(b/2)) = 4·√(2b)·2^(b/2) ≤ 40·√(b+1)·2^(b/2).
    have h_eq : Real.sqrt (2 * (b : ℝ)) * (4 * (2 : ℝ) ^ ((b : ℝ) / 2)) =
                4 * Real.sqrt (2 * (b : ℝ)) * (2 : ℝ) ^ ((b : ℝ) / 2) := by ring
    rw [h_eq]
    exact h_short_bound_le_total
  · -- Case M > b: split at ρ = b+1.
    push_neg at hMb
    -- Split: range (M+1) = range (b+1) ⊔ Ico (b+1) (M+1).
    have h_split : ∑ ρ ∈ Finset.range (M + 1),
        Real.sqrt ((ρ : ℝ) + b) *
          min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) =
        (∑ ρ ∈ Finset.range (b + 1),
          Real.sqrt ((ρ : ℝ) + b) *
            min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2))) +
        ∑ ρ ∈ Finset.Ico (b + 1) (M + 1),
          Real.sqrt ((ρ : ℝ) + b) *
            min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) := by
      simp only [Finset.range_eq_Ico]
      rw [Finset.sum_Ico_consecutive _ (by omega : 0 ≤ b + 1) (by omega : b + 1 ≤ M + 1)]
    rw [h_split]
    -- Bound each piece.
    have h_sqrt_2b_nn : 0 ≤ Real.sqrt (2 * (b : ℝ)) := Real.sqrt_nonneg _
    -- Short part: ≤ 4·√(2b)·2^(b/2).
    have h_short :
        ∑ ρ ∈ Finset.range (b + 1),
          Real.sqrt ((ρ : ℝ) + b) *
            min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) ≤
        4 * Real.sqrt (2 * (b : ℝ)) * (2 : ℝ) ^ ((b : ℝ) / 2) := by
      have h_term_le : ∀ ρ ∈ Finset.range (b + 1),
          Real.sqrt ((ρ : ℝ) + b) *
            min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) ≤
          Real.sqrt (2 * (b : ℝ)) * (2 : ℝ) ^ ((ρ : ℝ) / 2) := by
        intro ρ hρ
        rw [Finset.mem_range] at hρ
        have hρ_le_b : (ρ : ℝ) ≤ b := by exact_mod_cast (show ρ ≤ b by omega)
        have h_min_eq : min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) =
                        (2 : ℝ) ^ ((ρ : ℝ) / 2) := by
          apply min_eq_left
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          linarith
        rw [h_min_eq]
        apply mul_le_mul_of_nonneg_right
        · apply Real.sqrt_le_sqrt; linarith
        · exact Real.rpow_nonneg h2_nn _
      refine le_trans (Finset.sum_le_sum h_term_le) ?_
      rw [← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left (apssv_geom_short b) h_sqrt_2b_nn
      linarith [this]
    -- Long part: bound term-wise without explicit reindex.
    -- For ρ ∈ Ico (b+1) (M+1):
    --   min = 2^(b - ρ/2) (since ρ > b).
    --   √(ρ+b) ≤ √(2b) + √(ρ-b) (sub-additivity of √).
    -- So term ≤ (√(2b) + √(ρ-b)) · 2^(b - ρ/2).
    have h_long_term_le : ∀ ρ ∈ Finset.Ico (b + 1) (M + 1),
        Real.sqrt ((ρ : ℝ) + b) *
            min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) ≤
        (Real.sqrt (2 * (b : ℝ)) + Real.sqrt ((ρ - b : ℕ) : ℝ)) *
            (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2) := by
      intro ρ hρ
      rw [Finset.mem_Ico] at hρ
      have hρ_gt : (b : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ.1
      have hρ_ge : b ≤ ρ := by omega
      have h_min_eq : min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) =
                      (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2) := by
        apply min_eq_right
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      rw [h_min_eq]
      apply mul_le_mul_of_nonneg_right
      · -- √(ρ+b) ≤ √(2b) + √(ρ-b).
        have hbρ : b ≤ ρ := by omega
        rw [show ((ρ : ℝ) + b) = 2 * (b : ℝ) + ((ρ - b : ℕ) : ℝ) by
          rw [Nat.cast_sub hbρ]; ring]
        rw [show Real.sqrt (2 * (b : ℝ)) + Real.sqrt ((ρ - b : ℕ) : ℝ) =
            Real.sqrt ((Real.sqrt (2 * (b : ℝ)) + Real.sqrt ((ρ - b : ℕ) : ℝ)) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_le_sqrt
        have h2bn : 0 ≤ Real.sqrt (2 * (b : ℝ)) := Real.sqrt_nonneg _
        have hτn : 0 ≤ Real.sqrt ((ρ - b : ℕ) : ℝ) := Real.sqrt_nonneg _
        have h2b_sq : Real.sqrt (2 * (b : ℝ)) ^ 2 = 2 * (b : ℝ) := by
          rw [Real.sq_sqrt (by positivity)]
        have hτ_sq : Real.sqrt ((ρ - b : ℕ) : ℝ) ^ 2 = ((ρ - b : ℕ) : ℝ) := by
          rw [Real.sq_sqrt (by positivity)]
        nlinarith [mul_nonneg h2bn hτn]
      · exact Real.rpow_nonneg h2_nn _
    have h_sqrt_2b_nn : 0 ≤ Real.sqrt (2 * (b : ℝ)) := Real.sqrt_nonneg _
    have h_long :
        ∑ ρ ∈ Finset.Ico (b + 1) (M + 1),
          Real.sqrt ((ρ : ℝ) + b) *
            min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) ≤
        4 * Real.sqrt (2 * (b : ℝ)) * (2 : ℝ) ^ ((b : ℝ) / 2) +
          10 * (2 : ℝ) ^ ((b : ℝ) / 2) := by
      refine le_trans (Finset.sum_le_sum h_long_term_le) ?_
      -- Split sum.
      rw [show
        ∑ ρ ∈ Finset.Ico (b + 1) (M + 1),
          (Real.sqrt (2 * (b : ℝ)) + Real.sqrt ((ρ - b : ℕ) : ℝ)) *
            (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2) =
        Real.sqrt (2 * (b : ℝ)) *
          (∑ ρ ∈ Finset.Ico (b + 1) (M + 1), (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2)) +
        ∑ ρ ∈ Finset.Ico (b + 1) (M + 1),
          Real.sqrt ((ρ - b : ℕ) : ℝ) * (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ρ _; ring]
      -- Reindex via Finset.sum_Ico_eq_sum_range.
      have h_reindex_geom :
          ∑ ρ ∈ Finset.Ico (b + 1) (M + 1), (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2) =
          (2 : ℝ) ^ ((b : ℝ) / 2) *
            ∑ τ ∈ Finset.Ico 1 (M - b + 1), (2 : ℝ) ^ (-(τ : ℝ) / 2) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        rw [show M + 1 - (b + 1) = M - b from by omega,
            show M - b + 1 - 1 = M - b from by omega]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; push_cast; ring
      have h_reindex_geom_sqrt :
          ∑ ρ ∈ Finset.Ico (b + 1) (M + 1),
            Real.sqrt ((ρ - b : ℕ) : ℝ) * (2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2) =
          (2 : ℝ) ^ ((b : ℝ) / 2) *
            ∑ τ ∈ Finset.Ico 1 (M - b + 1), Real.sqrt (τ : ℝ) * (2 : ℝ) ^ (-(τ : ℝ) / 2) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        rw [show M + 1 - (b + 1) = M - b from by omega,
            show M - b + 1 - 1 = M - b from by omega]
        apply Finset.sum_congr rfl
        intro k _
        have h_sub : ((b + 1 + k - b : ℕ) : ℝ) = ((1 + k : ℕ) : ℝ) := by
          congr 1; omega
        rw [h_sub]
        rw [show ((b : ℝ) - ((b + 1 + k : ℕ) : ℝ) / 2) =
              ((b : ℝ) / 2) + (-((1 + k : ℕ) : ℝ) / 2) by push_cast; ring]
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring
      rw [h_reindex_geom, h_reindex_geom_sqrt]
      -- Apply geom_tail (≤ 4) and geom_tail_sqrt (≤ 10).
      have h_tail := apssv_geom_tail (M - b)
      have h_tail_sqrt := apssv_geom_tail_sqrt (M - b)
      have step_long_1 :
          Real.sqrt (2 * (b : ℝ)) *
              ((2 : ℝ) ^ ((b : ℝ) / 2) *
                ∑ τ ∈ Finset.Ico 1 (M - b + 1), (2 : ℝ) ^ (-(τ : ℝ) / 2)) ≤
          Real.sqrt (2 * (b : ℝ)) * ((2 : ℝ) ^ ((b : ℝ) / 2) * 4) := by
        apply mul_le_mul_of_nonneg_left _ h_sqrt_2b_nn
        exact mul_le_mul_of_nonneg_left h_tail h_2pow_b_nn
      have step_long_2 :
          (2 : ℝ) ^ ((b : ℝ) / 2) *
              ∑ τ ∈ Finset.Ico 1 (M - b + 1), Real.sqrt (τ : ℝ) * (2 : ℝ) ^ (-(τ : ℝ) / 2) ≤
          (2 : ℝ) ^ ((b : ℝ) / 2) * 10 :=
        mul_le_mul_of_nonneg_left h_tail_sqrt h_2pow_b_nn
      have h_combined_long := add_le_add step_long_1 step_long_2
      refine le_trans h_combined_long ?_
      ring_nf
      linarith
    -- Combine short + long ≤ 4·√(2b)·2^(b/2) + (4·√(2b)·2^(b/2) + 10·2^(b/2))
    --                    = 8·√(2b)·2^(b/2) + 10·2^(b/2) ≤ 40·√(b+1)·2^(b/2).
    have h_combined := add_le_add h_short h_long
    refine le_trans h_combined ?_
    have h_b1_ge_1 : 1 ≤ Real.sqrt ((b : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (b : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (b : ℝ) := by positivity
        linarith
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt ((b : ℝ) + 1) := Real.sqrt_le_sqrt h1
    nlinarith [h_sqrt_2b_le, h_sqrt_2_le_2, h_sqrt_b1_nn, h_2pow_b_nn, h_sqrt_2_nn,
      h_b1_ge_1, mul_nonneg h_sqrt_b1_nn h_2pow_b_nn,
      mul_nonneg h_sqrt_2b_nn h_2pow_b_nn]

/-- Conversion: `apssvB k + 1 ≤ 4 · log k / log 2` for `k ≥ 2`, used to bound
`√(apssvB k + 1)` by a constant multiple of `√(log k)`. -/
@[category API, AMS 11]
lemma apssv_b_le_log (k : ℕ) (hk : 2 ≤ k) :
    (apssvB k : ℝ) + 1 ≤ 4 * Real.log k / Real.log 2 := by
  unfold apssvB
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk_pos : 0 < k := by omega
  have h_logk_ge_log2 : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hk)
  have h_log2_le_logb : (Nat.log2 (2 * k) : ℝ) ≤ Real.logb 2 ((2 * k : ℕ) : ℝ) :=
    Real.log2_le_logb _
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk_pos.ne'
  have h_logb_eq : Real.logb 2 ((2 * k : ℕ) : ℝ) = 1 + Real.log k / Real.log 2 := by
    rw [Real.logb]
    push_cast
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hk_ne, add_div]
    rw [div_self h_log2_pos.ne']
  rw [h_logb_eq] at h_log2_le_logb
  -- Now: Nat.log2 (2*k) ≤ 1 + log k / log 2.
  -- So Nat.log2 (2*k) + 1 + 1 ≤ 2 + 1 + log k / log 2 = 3 + log k / log 2.
  -- And 3 + log k / log 2 ≤ 4 · log k / log 2 iff 3 ≤ 3 · log k / log 2 iff 1 ≤ log k / log 2 iff log 2 ≤ log k. ✓
  have h_logk_div_ge : 1 ≤ Real.log k / Real.log 2 := by
    rw [le_div_iff₀ h_log2_pos]
    linarith
  push_cast
  have h_step : (Nat.log2 (2 * k) : ℝ) + 1 + 1 ≤ 3 + Real.log k / Real.log 2 := by linarith
  have h_div : 4 * Real.log k / Real.log 2 = 4 * (Real.log k / Real.log 2) := by ring
  rw [h_div]
  linarith

@[category API, AMS 11]
lemma apssv_sum_T_to_levels (T : Finset (ℕ × ℕ)) (f : ℕ → ℝ) (M : ℕ)
    (hf : ∀ ρ, 0 ≤ f ρ)
    (hT_lev : ∀ pr ∈ T, pr.2 ≤ M)
    (hmult : ∀ ρ : ℕ, (T.filter fun pr => pr.2 = ρ).card ≤ 2) :
    ∑ x ∈ T, f x.2 ≤ 2 * ∑ ρ ∈ Finset.range (M + 1), f ρ := by
  -- Partition T by level: T = ⋃_{ρ ≤ M} (T.filter (·.2 = ρ)).
  have h_T_eq : T =
      (Finset.range (M + 1)).biUnion (fun ρ => T.filter fun pr => pr.2 = ρ) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_biUnion]
      exact ⟨x.2, Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_lev x hx)),
        Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · intro hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨ρ, _, hx_filter⟩ := hx
      exact (Finset.mem_filter.mp hx_filter).1
  have h_disjoint :
      Set.PairwiseDisjoint (↑(Finset.range (M + 1)))
        (fun ρ => T.filter fun pr => pr.2 = ρ) := by
    intro ρ _ ρ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  calc ∑ x ∈ T, f x.2
      = ∑ x ∈ (Finset.range (M + 1)).biUnion
            (fun ρ => T.filter fun pr => pr.2 = ρ), f x.2 := by rw [← h_T_eq]
    _ = ∑ ρ ∈ Finset.range (M + 1),
            ∑ x ∈ T.filter fun pr => pr.2 = ρ, f x.2 :=
        Finset.sum_biUnion h_disjoint
    _ ≤ ∑ ρ ∈ Finset.range (M + 1), 2 * f ρ := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        have hcard : (T.filter fun pr => pr.2 = ρ).card ≤ 2 := hmult ρ
        calc ∑ x ∈ T.filter fun pr => pr.2 = ρ, f x.2
            = ∑ x ∈ T.filter fun pr => pr.2 = ρ, f ρ := by
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [Finset.mem_filter] at hx
              rw [hx.2]
          _ = ((T.filter fun pr => pr.2 = ρ).card : ℝ) * f ρ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 2 * f ρ := by
              apply mul_le_mul_of_nonneg_right _ (hf ρ)
              exact_mod_cast hcard
    _ = 2 * ∑ ρ ∈ Finset.range (M + 1), f ρ := by rw [← Finset.mul_sum]

/-- Reduction: the block bound implies the partial-sum bound $\|S_N(k)\| \ll \sqrt{k \log k}$.

Given the dyadic decomposition (`apssv_dyadic_decomp`) and the block bound, the partial
sum has at most $\log_2 N$ blocks. Each block contributes at most
$C \sqrt{r+b} \cdot \min\{2^{r/2}, 2^{b-r/2}\}$. Summing the geometric envelope across $r$:
$$ \sum_{r=0}^{\log_2 N} \sqrt{r+b} \cdot \min\{2^{r/2}, 2^{b-r/2}\} \ll \sqrt{b} \cdot 2^{b/2}
   \ll \sqrt{\log k} \cdot \sqrt{k}. $$ -/
@[category API, AMS 11]
lemma apssv_partial_sum_bound (η : List Bool → Bool) (C : ℝ) (hC : 0 < C)
    (hbb : apssvBlockBound η C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k n : ℕ, 2 ≤ k →
      ‖∑ j ∈ Finset.range n, e ((k : ℝ) * apssvX η j)‖ ≤
        C' * Real.sqrt ((k : ℝ) * Real.log k) := by
  -- The constant `C' = 800 · C / √(log 2)` is a deliberately loose upper bound to leave
  -- ample slack in every estimate. The chain of multiplicative constants is:
  --   • 2  — per-level multiplicity ≤ 2 (from `apssv_sum_T_to_levels`).
  --   • 40 — geometric envelope (from `apssv_geom_envelope`; tight value ≈ 22).
  --   • 2  — `2^(b/2) ≤ 2·√k` (from `apssv_two_pow_b_le`).
  --   • 2  — `√(b+1) ≤ 2·√(log k)/√(log 2)` (from `apssv_b_le_log`).
  -- Tight product: 2 · 40 · 2 · 2 · C / √(log 2) = 320 · C / √(log 2). The factor of
  -- 800 / 320 = 2.5 absorbs rounding, the 8√2 + 10 ≈ 21.3 ≤ 40 slack in the envelope,
  -- and the √b ≤ √(b+1) extension. We'd rather have a slightly loose constant than
  -- chase tight asymptotic constants — the *qualitative* bound `O(√(k log k))` is
  -- what matters for the Erdős 987 application.
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_sqrt_log2_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr h_log2_pos
  refine ⟨800 * C / Real.sqrt (Real.log 2), ?_, ?_⟩
  · positivity
  intro k n hk2
  have hk1 : 1 ≤ k := by omega
  have hk_pos : 0 < k := by omega
  have hk_real_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have h_logk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk2)
  have h_logk_ge_log2 : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hk2)
  -- Step 1: dyadic decomposition.
  obtain ⟨T, hT_lev, hT_mult, hT_eq⟩ := apssv_dyadic_decomp η k n
  rw [hT_eq]
  refine le_trans (norm_sum_le _ _) ?_
  set b := apssvB k with hb_def
  set f : ℕ → ℝ := fun ρ =>
    Real.sqrt ((ρ : ℝ) + b) * min ((2 : ℝ) ^ ((ρ : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (ρ : ℝ) / 2))
    with hf_def
  have hf_nn : ∀ ρ, 0 ≤ f ρ := by
    intro ρ
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply le_min
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  -- Step 2: per-block bound from hbb.
  have h_per_block : ∀ pr ∈ T, ‖apssvBlockSum η pr.1 pr.2 k‖ ≤ C * f pr.2 := by
    intro pr _
    have h := hbb k pr.1 pr.2 hk1
    show ‖apssvBlockSum η pr.1 pr.2 k‖ ≤ C * (Real.sqrt ((pr.2 : ℝ) + b) *
      min ((2 : ℝ) ^ ((pr.2 : ℝ) / 2)) ((2 : ℝ) ^ ((b : ℝ) - (pr.2 : ℝ) / 2)))
    rw [← mul_assoc]; exact h
  refine le_trans (Finset.sum_le_sum (fun pr hpr => h_per_block pr hpr)) ?_
  rw [← Finset.mul_sum]
  -- Step 3: chain the helpers.
  have h_levels := apssv_sum_T_to_levels T f n hf_nn hT_lev hT_mult
  have h_env := apssv_geom_envelope b n
  have h_chain : ∑ pr ∈ T, f pr.2 ≤ 80 * Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2) := by
    calc ∑ pr ∈ T, f pr.2
        ≤ 2 * ∑ ρ ∈ Finset.range (n + 1), f ρ := h_levels
      _ ≤ 2 * (40 * Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h_env (by norm_num)
      _ = 80 * Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2) := by ring
  -- Step 4: 2^(b/2) ≤ 2·√k via apssv_two_pow_b_le.
  have h_2pow : (2 : ℝ) ^ ((b : ℝ) / 2) ≤ 2 * Real.sqrt (k : ℝ) := by
    have h_b_le : (2 : ℝ) ^ b ≤ 4 * k := by
      have h := apssv_two_pow_b_le k hk1
      rwa [Real.rpow_natCast] at h
    have h_eq : (2 : ℝ) ^ ((b : ℝ) / 2) = Real.sqrt ((2 : ℝ) ^ b) := by
      rw [apssv_two_rpow_half]
      rw [show ((2 : ℝ) ^ b) = ((Real.sqrt 2) ^ b) ^ 2 from by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]]
      rw [Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
    rw [h_eq]
    have h_sqrt_4k : Real.sqrt ((4 : ℝ) * k) = 2 * Real.sqrt (k : ℝ) := by
      rw [show ((4 : ℝ) * k) = 2 ^ 2 * k from by norm_num,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← h_sqrt_4k]
    exact Real.sqrt_le_sqrt h_b_le
  -- Step 5: √(b+1) ≤ 2·√(log k)/√(log 2) via apssv_b_le_log.
  have h_b_log : Real.sqrt ((b : ℝ) + 1) ≤ 2 * Real.sqrt (Real.log k) / Real.sqrt (Real.log 2) := by
    have h_le : Real.sqrt ((b : ℝ) + 1) ≤ Real.sqrt (4 * Real.log k / Real.log 2) :=
      Real.sqrt_le_sqrt (apssv_b_le_log k hk2)
    have h_eq : Real.sqrt (4 * Real.log k / Real.log 2) =
                2 * Real.sqrt (Real.log k) / Real.sqrt (Real.log 2) := by
      rw [show (4 * Real.log k / Real.log 2 : ℝ) = 4 * (Real.log k / Real.log 2) by ring]
      rw [show ((4 : ℝ)) = 2 ^ 2 by norm_num]
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.sqrt_div h_logk_pos.le]
      ring
    rw [← h_eq]; exact h_le
  -- Step 6: combine to get √(b+1) · 2^(b/2) ≤ 4 · √(k log k) / √(log 2).
  have h_combined : Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2) ≤
      4 * Real.sqrt ((k : ℝ) * Real.log k) / Real.sqrt (Real.log 2) := by
    have h_2pow_nn : 0 ≤ (2 : ℝ) ^ ((b : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have h_lhs_le := mul_le_mul h_b_log h_2pow h_2pow_nn (by positivity)
    refine le_trans h_lhs_le ?_
    have h_sqrt_klog :
        2 * Real.sqrt (Real.log k) / Real.sqrt (Real.log 2) * (2 * Real.sqrt (k : ℝ)) =
        4 * (Real.sqrt (Real.log k) * Real.sqrt (k : ℝ)) / Real.sqrt (Real.log 2) := by
      field_simp; ring
    rw [h_sqrt_klog]
    have h_mul_sqrt : Real.sqrt (Real.log k) * Real.sqrt (k : ℝ) =
                      Real.sqrt ((k : ℝ) * Real.log k) := by
      rw [← Real.sqrt_mul h_logk_pos.le, mul_comm]
    rw [h_mul_sqrt]
  -- Step 7: assemble final bound.
  have hC_nn : 0 ≤ C := hC.le
  have h_kl_nn : 0 ≤ Real.sqrt ((k : ℝ) * Real.log k) := Real.sqrt_nonneg _
  calc C * ∑ pr ∈ T, f pr.2
      ≤ C * (80 * Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h_chain hC_nn
    _ = 80 * C * (Real.sqrt ((b : ℝ) + 1) * (2 : ℝ) ^ ((b : ℝ) / 2)) := by ring
    _ ≤ 80 * C * (4 * Real.sqrt ((k : ℝ) * Real.log k) / Real.sqrt (Real.log 2)) :=
          mul_le_mul_of_nonneg_left h_combined (by positivity)
    _ = 320 * C * Real.sqrt ((k : ℝ) * Real.log k) / Real.sqrt (Real.log 2) := by ring
    _ ≤ 800 * C / Real.sqrt (Real.log 2) * Real.sqrt ((k : ℝ) * Real.log k) := by
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ h_sqrt_log2_pos.le
          nlinarith [h_kl_nn, hC_nn]

/- ## Other variants: APSSV26b upper bound, finite-distinct-points, and helpers -/

/-- An internal OpenAI model (see [APSSV26b, §3]) proved that there exists an infinite sequence
$x_1, x_2, \ldots \in (0, 1)$ such that
$\sup_n \left\lvert \sum_{j \le n} e(k x_j) \right\rvert \ll (k \log k)^{1/2}$ for all $k \ge 1$
(in particular $A_k \ll (k \log k)^{1/2}$).

**Construction (randomized binary scrambling).** Let $\eta_u \in \{0,1\}$ for each finite
binary word $u$ (including $\emptyset$) be independent Bernoulli(1/2) random variables.
Writing $n = \sum_{i \ge 0} d_i 2^i$ in binary, define
$$ x_n := \sum_{i \ge 0} \frac{d_i \oplus \eta_{d_0 \cdots d_{i-1}}}{2^{i+1}}, $$
i.e. read the bits of $n$ from low to high, and at stage $i$ the prefix $d_0 \cdots d_{i-1}$
selects which η-bit XORs the next digit. If all $\eta_u = 0$ this is the binary van der Corput
sequence; the random scrambling makes each dyadic-block exponential sum a sum of independent
centered random variables.

**Proof outline (Theorem 3.1 of [APSSV26b]):**
1. **Block decomposition**: For $P \ge 0$ and $r \ge 0$, write the dyadic block
   $\sum_{n=P 2^r}^{(P+1) 2^r - 1} e(k x_n) = B_{P,r}(k)$ where the form of $x_n$ on this block
   factorizes into $r$ scrambled-prefix digits $j_r(w) \in \{0, \ldots, 2^r - 1\}$ (a random
   bijection from $\{0,1\}^r$) plus a tail $T_{w,P}$ shared across $w$.
2. **Block bound** (Proposition 3.5): $|B_{P,r}(k)| \ll \sqrt{r + b} \cdot \min\{2^{r/2}, 2^{b-r/2}\}$
   where $b = b(k)$ (formally `apssvB k = Nat.log2 (2k) + 1` here; mathematically
   $\lceil \log_2(2k) \rceil$, the formal version is $\lfloor \log_2(2k) \rfloor + 1$,
   which matches except at exact powers of two and weakens the bound harmlessly).
   This uses Hoeffding/Bernstein on the centered sum over $w \in \{0,1\}^r$.
3. **Dyadic decomposition**: Any $N$ in binary $N = \sum b_i 2^i$ decomposes $[0, N)$ into
   blocks $[P_i 2^{r_i}, (P_i + 1) 2^{r_i})$ with $r_i$ ranging over the binary digits of $N$.
   Triangle inequality on these blocks plus the per-block bound yields
   $\sup_N |S_N(k)| \ll \sqrt{k \log k}$.
4. **Existence from positive probability**: The random construction has the required bound
   with positive probability, so a deterministic sequence with the bound exists.

**Status**: closed. All four steps are fully formalized: `apssv_partial_sum_bound`,
`apssv_geom_envelope`, `apssv_dyadic_decomp` (steps 1, 3, 4), and `apssv_exists_block_bound`
(step 2 — built on the probability infrastructure: random variables on `List Bool → Bool`
via `apssvEtaMeasure`, conditional independence via `Kernel.HasSubgaussianMGF`, and Tannery's
union bound across the countable parameter family `(k, P, r)`).

Note: the bound is restricted to $k \ge 2$ since $\log 1 = 0$ would make the RHS vanish at
$k = 1$, while the LHS $\|\sum_{j < n} e(x_j)\|$ can equal $1$ (e.g. for $n = 1$). The
asymptotic statement $A_k \ll (k \log k)^{1/2}$ is captured for all sufficiently large $k$. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.sqrt_log_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (C : ℝ) (_ : 0 < C),
      ∀ k n : ℕ, 2 ≤ k → ‖∑ j ∈ range n, e (k * x j)‖ ≤ C * Real.sqrt (k * Real.log k) := by
  -- Get η satisfying the block bound (Prop 3.5) AND having apssvX η j ∈ Ioo 0 1 for all j.
  obtain ⟨η, C₀, hC₀, hbb, hxIoo⟩ := apssv_exists_block_bound
  -- Reduce to the partial-sum bound.
  obtain ⟨C', hC', hbound⟩ := apssv_partial_sum_bound η C₀ hC₀ hbb
  -- Use apssvX η directly as the witness sequence.
  refine ⟨apssvX η, hxIoo, C', hC', ?_⟩
  intro k n hk2
  exact hbound k n hk2

/-- **Question 2 (parts.ii)**: there exists a sequence $(x_n) \in (0, 1)$ and a
bound $b(k) = o(k)$ such that $A x k \le b k$ eventually. Direct corollary of
`sqrt_log_upper_bound` (which gives a $\sqrt{k \log k}$ bound) plus the
asymptotic $\sqrt{k \log k} = o(k)$. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.parts.ii :
    answer(True) ↔ ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (b : ℕ → ℝ),
      b =o[atTop] (fun k : ℕ => (k : ℝ)) ∧ ∀ᶠ k : ℕ in atTop, A x k ≤ ((b k : ℝ) : EReal) := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  -- Get the witness from sqrt_log_upper_bound.
  obtain ⟨x, hx, C, hC, hbound⟩ := erdos_987.variants.sqrt_log_upper_bound
  -- The bound function: b k = C · √(k · log k).
  refine ⟨x, hx, fun k => C * Real.sqrt ((k : ℝ) * Real.log k), ?_, ?_⟩
  · -- Asymptotic: b k = o(k). Strategy: log k = o(k) ⇒ k·log k = o(k²) ⇒ √(k·log k) = o(k).
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hC' : 0 < C + 1 := by linarith
    -- Choose threshold (ε/(C+1))² for the log k = o(k) bound.
    have hδ : (0 : ℝ) < (ε / (C + 1))^2 := by positivity
    have h_log_lt : (fun k : ℕ => Real.log k) =o[atTop] (fun k : ℕ => (k : ℝ)) :=
      Real.isLittleO_log_id_atTop.natCast_atTop
    have h_log_bd := (Asymptotics.isLittleO_iff.mp h_log_lt) hδ
    filter_upwards [h_log_bd, Filter.eventually_ge_atTop 1] with k h_lk hk_ge
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_ge
    have h_log_nn : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk_ge)
    -- log k ≤ (ε/(C+1))² · k.
    have h_lk' : Real.log k ≤ (ε / (C + 1))^2 * k := by
      have h1 := h_lk
      rw [Real.norm_of_nonneg h_log_nn,
          Real.norm_of_nonneg hk_pos.le] at h1
      linarith
    -- Squared: k · log k ≤ ((ε/(C+1)) · k)².
    have h_klog_le : (k : ℝ) * Real.log k ≤ ((ε / (C + 1)) * k)^2 := by
      have : (k : ℝ) * Real.log k ≤ (k : ℝ) * ((ε / (C + 1))^2 * k) :=
        mul_le_mul_of_nonneg_left h_lk' hk_pos.le
      nlinarith
    -- √(k·log k) ≤ (ε/(C+1)) · k.
    have h_sqrt_le : Real.sqrt ((k : ℝ) * Real.log k) ≤ (ε / (C + 1)) * k := by
      have h_sqrt := Real.sqrt_le_sqrt h_klog_le
      rwa [Real.sqrt_sq (by positivity)] at h_sqrt
    -- Final: ‖C·√(k·log k)‖ ≤ ε · ‖k‖.
    have h_C_sqrt_nn : 0 ≤ C * Real.sqrt ((k : ℝ) * Real.log k) := by positivity
    rw [Real.norm_of_nonneg h_C_sqrt_nn, Real.norm_of_nonneg hk_pos.le]
    have h_step : C * Real.sqrt ((k : ℝ) * Real.log k) ≤ C * ((ε / (C + 1)) * k) :=
      mul_le_mul_of_nonneg_left h_sqrt_le hC.le
    have h_C_ratio : C / (C + 1) ≤ 1 := by rw [div_le_one hC']; linarith
    have h_final : C * ((ε / (C + 1)) * k) ≤ ε * k := by
      have : C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
      have h2 : C * ((ε / (C + 1)) * k) = (C / (C + 1)) * ε * k := by
        rw [show C * ((ε / (C + 1)) * k) = (C * (ε / (C + 1))) * k from by ring, this]
      rw [h2]
      have : (C / (C + 1)) * ε * k ≤ 1 * ε * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_C_ratio hε.le) hk_pos.le
      linarith
    linarith
  · -- A x k ≤ b k eventually (for k ≥ 2).
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    apply A_le_of_uniform_bound x k _ (fun n => hbound k n hk)

/-- Liu [Li69] showed that, for any $\epsilon > 0$, $A_k \gg k^{1 - \epsilon}$ infinitely often
under the additional assumption that there are only a finite number of distinct points. Clunie
observed in the Mathscinet review of [Li69] that under this assumption in fact $A_k = \infty$
infinitely often (the version stated here).

**Proof alignment with Liu/Clunie.** The intended argument is essentially Clunie's stronger
observation, not Liu's quantitative $k^{1-\varepsilon}$ bound. Outline:

1. By `Finset.exists_freq_natCast_mul_sub_round_lt`, infinitely many $k$ have $|k y_i -
   \mathrm{round}(k y_i)| < \varepsilon$ for all values $y_i$ of $x$ simultaneously, where
   $\varepsilon = 1/(4\pi)$ ensures $\|e(k y_i) - 1\| < 1/2$ (via `e_sub_one_norm_le`).
2. For such $k$, $\|\sum_{j < n} e(k x_j)\| \ge n - n/2 = n/2 \to \infty$, so $A_k = \infty$.

This matches Clunie's "in fact $A_k = \infty$ i.o." observation. Liu's original bound
$A_k \gg k^{1-\varepsilon}$ requires a more delicate analysis that tracks how the
simultaneous-Dirichlet $\varepsilon$ scales with $k$; the simultaneous Dirichlet step here
is the same tool, just used qualitatively. -/
@[category research solved, AMS 11 40 42]
theorem erdos_987.variants.finite_distinct_points
    (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : (Set.range x).Finite) :
    ∃ᶠ k : ℕ in atTop, A x k = ⊤ := by
  let Y : Finset ℝ := hfin.toFinset
  have hxY : ∀ j, x j ∈ Y := fun j => hfin.mem_toFinset.mpr ⟨j, rfl⟩
  have hε₀ : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
  have hsim := Finset.exists_freq_natCast_mul_sub_round_lt Y hε₀
  refine hsim.mono fun k hk_bd => ?_
  -- Step 1: For each j, ‖e (k x_j) - 1‖ < 1/2.
  have hδ : ∀ j : ℕ, ‖e ((k : ℝ) * x j) - 1‖ < 1 / 2 := by
    intro j
    have hkx := hk_bd (x j) (hxY j)
    have h1 := e_sub_one_norm_le ((k : ℝ) * x j)
    have hπ_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have h2 : 2 * Real.pi * |(k : ℝ) * x j - round ((k : ℝ) * x j)| <
        2 * Real.pi * (1 / (4 * Real.pi)) :=
      mul_lt_mul_of_pos_left hkx hπ_pos
    have h3 : 2 * Real.pi * (1 / (4 * Real.pi)) = 1 / 2 := by
      have : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    linarith
  -- Step 2: Each partial sum has modulus ≥ n/2.
  have hpartial : ∀ n : ℕ, (n : ℝ) / 2 ≤ ‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ := by
    intro n
    -- Decompose ∑ e = n + ∑(e - 1).
    have hsum_eq : ∑ j ∈ range n, e ((k : ℝ) * x j) =
        (n : ℂ) + ∑ j ∈ range n, (e ((k : ℝ) * x j) - 1) := by
      rw [show ((n : ℂ)) = ∑ _ ∈ range n, (1 : ℂ) from by simp]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- Triangle bound on ∑(e - 1).
    have hdiff : ‖∑ j ∈ range n, (e ((k : ℝ) * x j) - 1)‖ ≤ (n : ℝ) / 2 := by
      calc ‖∑ j ∈ range n, (e ((k : ℝ) * x j) - 1)‖
          ≤ ∑ j ∈ range n, ‖e ((k : ℝ) * x j) - 1‖ := norm_sum_le _ _
        _ ≤ ∑ _ ∈ range n, (1 / 2 : ℝ) := sum_le_sum (fun j _ => (hδ j).le)
        _ = (n : ℝ) / 2 := by simp; ring
    -- Reverse triangle: ‖n‖ ≤ ‖n + S‖ + ‖S‖, so ‖n + S‖ ≥ ‖n‖ - ‖S‖.
    let S := ∑ j ∈ range n, (e ((k : ℝ) * x j) - 1)
    have hntri : ‖((n : ℂ) : ℂ)‖ ≤ ‖(n : ℂ) + S‖ + ‖S‖ := by
      have h := norm_add_le ((n : ℂ) + S) (-S)
      rw [show ((n : ℂ) + S) + -S = (n : ℂ) from by ring, norm_neg] at h
      exact h
    have hncast : ‖((n : ℂ) : ℂ)‖ = (n : ℝ) := by simp
    rw [hsum_eq]
    show (n : ℝ) / 2 ≤ ‖(n : ℂ) + S‖
    linarith
  -- Step 3: A x k = ⊤ via limsup of n/2 → ⊤.
  rw [A]
  refine top_le_iff.mp ?_
  have h_sub : ∀ n : ℕ, (((n : ℝ) / 2 : ℝ) : EReal) ≤
      ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal) := by
    intro n
    exact_mod_cast hpartial n
  have h_tendsto : Tendsto (fun n : ℕ => (((n : ℝ) / 2 : ℝ) : EReal)) atTop (nhds ⊤) :=
    EReal.tendsto_coe_nhds_top_iff.mpr
      (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
        tendsto_natCast_atTop_atTop)
  calc (⊤ : EReal) = atTop.limsup (fun n : ℕ => (((n : ℝ) / 2 : ℝ) : EReal)) :=
        h_tendsto.limsup_eq.symm
    _ ≤ atTop.limsup (fun n : ℕ => ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall h_sub)

end Erdos987
