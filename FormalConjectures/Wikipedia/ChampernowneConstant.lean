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
# Champernowne's Constant

D. G. Champernowne (1933) introduced the real constant
$$C_{10} = 0.12345678910111213\dots = \sum_{k=0}^{\infty} \frac{d_k}{10^{k+1}},$$
built by concatenating the decimal expansions of $1, 2, 3, \dots$ in increasing order
(OEIS A033307),
and established base-$10$ normality of $C_{10}$. Kurt Mahler (1937) proved that $C_{10}$ is
transcendental over $\mathbb{Q}$, and Masaaki Amou (1991) established that its irrationality
measure equals $\mu(C_{10}) = 10$.

Whether $C_{10}$ is normal in bases other than powers of $10$—for instance in base $9$—or is
normal across every integer base $b \ge 2$ remains open (note that normality in base $10$ already
entails normality in every power base $10^r$ by Maxfield 1953).

*References:*
- [Wikipedia: Champernowne constant](https://en.wikipedia.org/wiki/Champernowne_constant)
- [OEIS A033307](https://oeis.org/A033307)
- D. G. Champernowne, *The construction of decimals normal in the scale of ten*, J. London Math.
  Soc. **8** (1933), 254–260.
- K. Mahler, *Arithmetische Eigenschaften einer Klasse von Dezimalbrüchen*, Proc. Kon. Nederl.
  Akad. Wetensch. **40** (1937), 421–428.
- J. E. Maxfield, *Normal $k$-tuples*, Pacific J. Math. **3** (1953), 189–196.
- M. Amou, *Approximation to certain transcendental decimal fractions by algebraic numbers*, J.
  Number Theory **37** (1991), 231–241.
-/

@[expose] public section

namespace ChampernowneConstant

/-- The initial $13$ decimal digits of $C_{10}$ equal $[1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 0, 1, 1]$. -/
@[category test, AMS 11]
theorem champernowneDigit_initial_thirteen :
    (List.range 13).map champernowneDigit = [1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 0, 1, 1] := by
  decide

/-- Every entry of `champernowneDigit` is strictly less than $10$. -/
@[category API, AMS 11]
theorem champernowneDigit_lt_ten (k : ℕ) : champernowneDigit k < 10 := by
  unfold champernowneDigit
  set L := (List.range (k + 1)).flatMap (fun j => (Nat.digits 10 (j + 1)).reverse)
  by_cases hk : k < L.length
  · rw [List.getD_eq_getElem _ _ hk]
    have hmem : L[k] ∈ L := List.getElem_mem hk
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨j, _, hjmem⟩
    rw [List.mem_reverse] at hjmem
    exact Nat.digits_lt_base (by omega) hjmem
  · rw [List.getD_eq_default _ _ (Nat.not_lt.mp hk)]
    omega

/-- The decimal series defining `champernowneConstant` is summable in $\mathbb{R}$. -/
@[category API, AMS 11]
theorem champernowneDigit_summable :
    Summable (fun k : ℕ => (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1)) := by
  have hterm_le : ∀ k : ℕ,
      (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1) ≤ (9 / 10 : ℝ) * (1 / 10 : ℝ) ^ k := by
    intro k
    have hd : champernowneDigit k ≤ 9 := Nat.lt_succ_iff.mp (champernowneDigit_lt_ten k)
    have hd' : (champernowneDigit k : ℝ) ≤ 9 := by exact_mod_cast hd
    have hpow : (9 : ℝ) / (10 : ℝ) ^ (k + 1) = (9 / 10 : ℝ) * (1 / 10 : ℝ) ^ k := by
      rw [pow_succ, one_div_pow]
      ring
    rw [← hpow]
    exact div_le_div_of_nonneg_right hd' (by positivity)
  exact Summable.of_nonneg_of_le (fun _ => by positivity) hterm_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

/-- Geometric-series bound on the tail of `champernowneConstant` starting at index $4$:
$\sum_{k=0}^\infty d_{k+4} / 10^{k+5} \le 10^{-4}$. -/
@[category API, AMS 11]
theorem champernowneConstant_tail_four_le :
    (∑' k : ℕ, (champernowneDigit (k + 4) : ℝ) / (10 : ℝ) ^ (k + 4 + 1)) ≤ 1 / 10000 := by
  have htail_bound : ∀ k : ℕ,
      (champernowneDigit (k + 4) : ℝ) / (10 : ℝ) ^ (k + 4 + 1) ≤
        (9 / 100000 : ℝ) * (1 / 10 : ℝ) ^ k := by
    intro k
    have hd : (champernowneDigit (k + 4) : ℝ) ≤ 9 := by
      exact_mod_cast Nat.lt_succ_iff.mp (champernowneDigit_lt_ten (k + 4))
    have hpow : (9 : ℝ) / (10 : ℝ) ^ (k + 4 + 1) = (9 / 100000 : ℝ) * (1 / 10 : ℝ) ^ k := by
      rw [pow_add, one_div_pow]
      ring
    rw [← hpow]
    exact div_le_div_of_nonneg_right hd (by positivity)
  have hgeom : Summable (fun k : ℕ => (9 / 100000 : ℝ) * (1 / 10 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc
    (∑' k : ℕ, (champernowneDigit (k + 4) : ℝ) / (10 : ℝ) ^ (k + 4 + 1))
        ≤ ∑' k : ℕ, (9 / 100000 : ℝ) * (1 / 10 : ℝ) ^ k :=
      ((champernowneDigit_summable.comp_injective (add_left_injective 4)).tsum_le_tsum
        htail_bound hgeom)
    _ = (9 / 100000 : ℝ) * (1 - 1 / 10 : ℝ)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 1 / 10000 := by norm_num

/-- Lower decimal bound $0.123 < C_{10}$. -/
@[category test, AMS 11]
theorem lt_champernowneConstant : (123 : ℝ) / 1000 < champernowneConstant := by
  have hsplit : champernowneConstant =
      (∑ k ∈ Finset.range 4, (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1)) +
        ∑' k : ℕ, (champernowneDigit (k + 4) : ℝ) / (10 : ℝ) ^ (k + 4 + 1) :=
    (champernowneDigit_summable.sum_add_tsum_nat_add 4).symm
  have hd0 : champernowneDigit 0 = 1 := by decide
  have hd1 : champernowneDigit 1 = 2 := by decide
  have hd2 : champernowneDigit 2 = 3 := by decide
  have hd3 : champernowneDigit 3 = 4 := by decide
  have hhead : ∑ k ∈ Finset.range 4, (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1) =
      1234 / 10000 := by
    simp [Finset.sum_range_succ, hd0, hd1, hd2, hd3]
    norm_num
  have htail_nonneg :
      0 ≤ ∑' k : ℕ, (champernowneDigit (k + 4) : ℝ) / (10 : ℝ) ^ (k + 4 + 1) :=
    tsum_nonneg (fun _ => by positivity)
  rw [hsplit, hhead]
  linarith

/-- Upper decimal bound $C_{10} < 0.124$. -/
@[category test, AMS 11]
theorem champernowneConstant_lt : champernowneConstant < (124 : ℝ) / 1000 := by
  have hsplit : champernowneConstant =
      (∑ k ∈ Finset.range 4, (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1)) +
        ∑' k : ℕ, (champernowneDigit (k + 4) : ℝ) / (10 : ℝ) ^ (k + 4 + 1) :=
    (champernowneDigit_summable.sum_add_tsum_nat_add 4).symm
  have hd0 : champernowneDigit 0 = 1 := by decide
  have hd1 : champernowneDigit 1 = 2 := by decide
  have hd2 : champernowneDigit 2 = 3 := by decide
  have hd3 : champernowneDigit 3 = 4 := by decide
  have hhead : ∑ k ∈ Finset.range 4, (champernowneDigit k : ℝ) / (10 : ℝ) ^ (k + 1) =
      1234 / 10000 := by
    simp [Finset.sum_range_succ, hd0, hd1, hd2, hd3]
    norm_num
  have htail_le := champernowneConstant_tail_four_le
  rw [hsplit, hhead]
  linarith

/--
**Champernowne's Theorem** (1933): Champernowne's decimal constant $C_{10}$ satisfies base-$10$
normality (`NormalNumber.IsNormalInBase 10`).
-/
@[category research solved, AMS 11]
theorem champernowne_normal_base_ten :
    NormalNumber.IsNormalInBase 10 champernowneConstant := by
  sorry

/--
**Mahler's Theorem** (1937): Champernowne's decimal constant $C_{10}$ is transcendental over
$\mathbb{Q}$.
-/
@[category research solved, AMS 11]
theorem mahler_champernowne_transcendental :
    Transcendental ℚ champernowneConstant := by
  sorry

/--
**Amou's Irrationality Measure Theorem** (1991): the irrationality exponent of $C_{10}$ equals
$10$ (compare `Constant7a.irrationalityExponent` in `FormalConjectures.OptimizationConstants.7a`),
so for every $\varepsilon > 0$, $C_{10}$ satisfies `LiouvilleWith (10 - ε)` and fails
`LiouvilleWith (10 + ε)`.
-/
@[category research solved, AMS 11]
theorem amou_champernowne_irrationality_measure :
    (∀ ε : ℝ, 0 < ε → LiouvilleWith (10 - ε) champernowneConstant) ∧
      (∀ ε : ℝ, 0 < ε → ¬ LiouvilleWith (10 + ε) champernowneConstant) := by
  sorry

/--
Is Champernowne's decimal constant $C_{10}$ normal in base $9$?
-/
@[category research open, question, AMS 11]
theorem champernowne_normal_base_nine :
    NormalNumber.IsNormalInBase 9 champernowneConstant := by
  sorry

/--
Is Champernowne's decimal constant $C_{10}$ absolutely normal (called simply *normal* on
Wikipedia), i.e. normal in every integer base $b \ge 2$?
-/
@[category research open, question, AMS 11]
theorem champernowne_absolutely_normal :
    NormalNumber.IsAbsolutelyNormal champernowneConstant := by
  sorry

end ChampernowneConstant
