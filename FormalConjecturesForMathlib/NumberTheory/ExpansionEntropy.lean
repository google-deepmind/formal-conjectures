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

public import FormalConjecturesForMathlib.Dynamics.SymbolicDynamics.BlockComplexity
public import FormalConjecturesForMathlib.NumberTheory.NormalNumber
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic

/-!
# Entropy of the expansions of a real number

The entropy of the continued fraction expansion of a real number $\xi$ and of its expansion in
an integer base $b$. Both are the entropy `SymbolicDynamics.blockEntropy` of the sequence of
digits.

A real number is rich in base $b$ if and only if its base-$b$ expansion has the maximal block
complexity $p(n) = b^n$ for all $n$. Then its entropy is the maximal value $\log b$. In
particular, this holds for numbers that are normal in base $b$.

*References:*
- [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
  Vol. 193. Cambridge University Press, 2012. Chapter 10.

## Main definitions

* `Real.partQuot`: the sequence of partial quotients of a real number.
* `Real.cfEntropy`: the entropy of the continued fraction expansion of a real number.
* `Real.baseEntropy`: the entropy of the base `b` expansion of a real number.

## Main statements

* `NormalNumber.isRichInBase_iff_blockComplexity`: a number is rich in base `b` if and only if
  its expansion has block complexity `b ^ n` for all `n`.
* `Real.baseEntropy_le`: the entropy of a base `b` expansion is at most `log b`.
* `NormalNumber.IsRichInBase.baseEntropy_eq`, `NormalNumber.IsNormalInBase.baseEntropy_eq`:
  rich and normal numbers have entropy `log b`.
* `NormalNumber.IsRichInBase.not_isEventuallyPeriodic`: the expansion of a rich number is not
  eventually periodic.
-/

@[expose] public section

open Filter SymbolicDynamics

open scoped ENNReal

namespace Real

/--
The sequence $(c_n)_{n \ge 1}$ of partial quotients of the continued fraction expansion
$\xi = [c_0; c_1, c_2, \ldots]$, indexed from $0$. The integer part $c_0$ is not part of the
sequence. The expansion of an irrational number never terminates, so the default value `0` is
never used for such $\xi$.
-/
noncomputable def partQuot (ξ : ℝ) (n : ℕ) : ℝ :=
  ((GenContFract.of ξ).partDens.get? n).getD 0

/-- The entropy $E(\xi)$ of the continued fraction expansion of $\xi$. -/
noncomputable def cfEntropy (ξ : ℝ) : EReal := blockEntropy (partQuot ξ)

/-- The entropy $E(\xi, b)$ of the base $b$ expansion of $\xi$. -/
noncomputable def baseEntropy (b : ℕ) (ξ : ℝ) : EReal :=
  blockEntropy (NormalNumber.digitSeq b ξ)

end Real

namespace NormalNumber

private theorem blocks_subset {b : ℕ} (hb : 1 ≤ b) (ξ : ℝ) (n : ℕ) :
    {w : Fin n → ℕ | ∃ k, ∀ i, w i = digitSeq b ξ (k + i)} ⊆ {w | ∀ i, w i < b} :=
  fun _ ⟨_, hk⟩ i => hk i ▸ Nat.mod_lt _ hb

private theorem encard_digits (b n : ℕ) : {w : Fin n → ℕ | ∀ i, w i < b}.encard = b ^ n := by
  have : {w : Fin n → ℕ | ∀ i, w i < b} = ↑(Fintype.piFinset fun _ : Fin n => Finset.range b) := by
    ext w
    simp
  rw [this, Set.encard_coe_eq_coe_finsetCard, Fintype.card_piFinset]
  simp

/-- A base-$b$ expansion has at most $b^n$ distinct blocks of length $n$. -/
theorem blockComplexity_digitSeq_le {b : ℕ} (hb : 1 ≤ b) (ξ : ℝ) (n : ℕ) :
    blockComplexity (digitSeq b ξ) n ≤ (b : ℝ≥0∞) ^ n := by
  simpa [blockComplexity, encard_digits] using
    ENat.toENNReal_le.2 (Set.encard_le_encard (blocks_subset hb ξ n))

/-- A real number is rich in base $b$ if and only if its base-$b$ expansion has $b^n$ distinct
blocks of length $n$ for every $n$. -/
theorem isRichInBase_iff_blockComplexity {b : ℕ} (hb : 1 ≤ b) (ξ : ℝ) :
    IsRichInBase b ξ ↔ ∀ n, blockComplexity (digitSeq b ξ) n = (b : ℝ≥0∞) ^ n := by
  refine ⟨fun h n => ?_, fun h n w hw => ?_⟩
  · have : {w : Fin n → ℕ | ∃ k, ∀ i, w i = digitSeq b ξ (k + i)} = {w | ∀ i, w i < b} :=
      (blocks_subset hb ξ n).antisymm fun w hw => (h n w hw).imp fun k hk i => (hk i).symm
    simp [blockComplexity, this, encard_digits]
  · have hfin : {w : Fin n → ℕ | ∀ i, w i < b}.Finite :=
      Set.finite_of_encard_eq_coe (encard_digits b n)
    have heq := (hfin.subset (blocks_subset hb ξ n)).eq_of_subset_of_encard_le
      (blocks_subset hb ξ n)
      (ENat.toENNReal_le.1 (by simpa [blockComplexity, encard_digits] using (h n).ge))
    obtain ⟨k, hk⟩ := (Set.ext_iff.1 heq w).2 hw
    exact ⟨k, fun i => (hk i).symm⟩

/-- A number that is normal in base $b$ has $b^n$ distinct blocks of length $n$ in its base-$b$
expansion. -/
theorem IsNormalInBase.blockComplexity_eq {b : ℕ} (hb : 1 ≤ b) {ξ : ℝ} (h : IsNormalInBase b ξ)
    (n : ℕ) : blockComplexity (digitSeq b ξ) n = (b : ℝ≥0∞) ^ n :=
  (isRichInBase_iff_blockComplexity hb ξ).1 h.isRichInBase n

private theorem log_pow_div {b : ℕ} (hb : 1 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    ((b : ℝ≥0∞) ^ n).log / (n : EReal) = (Real.log b : EReal) := by
  have : (b : ℝ≥0∞) ^ n = ENNReal.ofReal ((b : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by positivity)]
    simp
  rw [this, ENNReal.log_ofReal_of_pos (by positivity), Real.log_pow, ← EReal.coe_coe_eq_natCast,
    ← EReal.coe_div, mul_div_cancel_left₀ _ (by exact_mod_cast hn)]

/-- The entropy of a base-$b$ expansion is at most $\log b$. -/
theorem _root_.Real.baseEntropy_le {b : ℕ} (hb : 1 ≤ b) (ξ : ℝ) :
    Real.baseEntropy b ξ ≤ (Real.log b : EReal) := by
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  rw [← log_pow_div hb (n := n) (by omega)]
  exact EReal.div_le_div_right_of_nonneg (by positivity)
    (ENNReal.log_le_log (blockComplexity_digitSeq_le hb ξ n))

/-- A number that is rich in base $b$ has base-$b$ entropy $\log b$. -/
theorem IsRichInBase.baseEntropy_eq {b : ℕ} (hb : 1 ≤ b) {ξ : ℝ} (h : IsRichInBase b ξ) :
    Real.baseEntropy b ξ = (Real.log b : EReal) := by
  refine Tendsto.limsup_eq (tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn => ?_)
  rw [(isRichInBase_iff_blockComplexity hb ξ).1 h n, log_pow_div hb (by omega)]

/-- A number that is normal in base $b$ has base-$b$ entropy $\log b$. -/
theorem IsNormalInBase.baseEntropy_eq {b : ℕ} (hb : 1 ≤ b) {ξ : ℝ} (h : IsNormalInBase b ξ) :
    Real.baseEntropy b ξ = (Real.log b : EReal) :=
  h.isRichInBase.baseEntropy_eq hb

/-- The base-$b$ expansion of a number that is rich in base $b \ge 2$ is not eventually
periodic. -/
theorem IsRichInBase.not_isEventuallyPeriodic {b : ℕ} (hb : 2 ≤ b) {ξ : ℝ}
    (h : IsRichInBase b ξ) : ¬ IsEventuallyPeriodic (digitSeq b ξ) := fun hp ↦ by
  obtain ⟨C, -, hC⟩ := hp.blockComplexity_le
  have := hC C
  rw [(isRichInBase_iff_blockComplexity (by omega) ξ).1 h C] at this
  exact this.not_gt (by exact_mod_cast Nat.lt_pow_self (by omega))

/-- The base-$b$ expansion of a number that is normal in base $b \ge 2$ is not eventually
periodic. -/
theorem IsNormalInBase.not_isEventuallyPeriodic {b : ℕ} (hb : 2 ≤ b) {ξ : ℝ}
    (h : IsNormalInBase b ξ) : ¬ IsEventuallyPeriodic (digitSeq b ξ) :=
  h.isRichInBase.not_isEventuallyPeriodic hb

end NormalNumber
