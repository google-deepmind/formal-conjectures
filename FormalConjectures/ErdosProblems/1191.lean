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
# Erdős Problem 1191

*References:*
- [erdosproblems.com/1191](https://www.erdosproblems.com/1191)
- [Er55] Stöhr, Alfred, *Gelöste und ungelöste Fragen über Basen der natürlichen Zahlenreihe. II*.
  J. Reine Angew. Math. 194 (1955), 111-140.
- [ErRe60] Erdős, P. and Rényi, A., *Additive properties of random sequences of positive integers*.
  Acta Arith. 6 (1960), 83-110.
- [HaRo66] Halberstam, H. and Roth, K. F., *Sequences. Vol. I*. (1966), xx+291.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Pa26] Parobek, Lucas, *Unconditional Diophantine Haar Closure, Exact Harmonic-Difference
  Conservation, and Multi-Octave Dyadic Budgets for Erdős Problem #1191*. (2026),
  [Manuscript PDF](https://github.com/doublegate/Erdos_1191/blob/main/paper/Parobek_2026-10-27_Erdos1191_Unconditional_Diophantine_Haar_Closure_Sidon_Sets.pdf),
  [github.com/doublegate/Erdos_1191](https://github.com/doublegate/Erdos_1191).
-/

@[expose] public section

open Filter Real

namespace Erdos1191

/--
Let $A\subset\mathbb{N}$ be an infinite Sidon set. Is it true that
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}=0?$$

Here $x$ runs over $\mathbb{N}$ and the $\liminf$ is taken in `ℝ≥0∞`, so that it is $\infty$
rather than $0$ when the sequence tends to infinity. See [Pa26] for exact harmonic-difference
conservation, cross-shell Laplace–Fejér bilinear inequalities, KKT convex-cone increment
minimization, and discrete Legendre–Fenchel / Diophantine Haar sawtooth identities reducing the
unconditional dyadic upper bound to $c_\infty^*(1^+) = 2$ with explicit finite-density sawtooth
sharpenings at bounded occupancy $\mu_1 = O(1)$.
-/
@[category research open, question, AMS 5 11]
theorem erdos_1191.parts.i : ∀ A : Set ℕ, A.Infinite → IsSidon A →
    liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop = 0 := by
  sorry

/--
Does there exist an infinite Sidon set $A$ such that
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^c>0$$
for some $c>0$?

A positive answer would also give a positive answer to Erdős Problem 39.
-/
@[category research open, question, AMS 5 11]
theorem erdos_1191.parts.ii : ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
    ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ c)) atTop := by
  sorry

/--
An affirmative answer to `erdos_1191.parts.i` immediately rules out the $c = 1/2$ case of
`erdos_1191.parts.ii`.
-/
@[category API, AMS 5 11]
theorem erdos_1191.variants.parts_i_implies_not_parts_ii_half
    (h : ∀ A : Set ℕ, A.Infinite → IsSidon A →
      liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop = 0) :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop := by
  rintro ⟨A, hAinf, hAsid, hpos⟩
  rw [h A hAinf hAsid] at hpos
  exact lt_irrefl 0 hpos

/--
Erdős proved (see for example [Er55] and [HaRo66]) that if $A$ is an infinite Sidon set then
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}\leq c$$
for some constant $c>0$. See also `erdos_158.variants.isSidon'`.
-/
@[category research solved, AMS 5 11]
theorem erdos_1191.variants.liminf_le {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    ∃ c > (0 : ℝ), liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop ≤
        ENNReal.ofReal c := by
  sorry

/--
An affirmative answer to `erdos_1191.parts.i` immediately implies `erdos_1191.variants.liminf_le`
with any $c > 0$.
-/
@[category API, AMS 5 11]
theorem erdos_1191.variants.parts_i_implies_liminf_le
    (h : ∀ A : Set ℕ, A.Infinite → IsSidon A →
      liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop = 0)
    {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    ∃ c > (0 : ℝ), liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop ≤
        ENNReal.ofReal c := by
  refine ⟨1, zero_lt_one, ?_⟩
  rw [h A hAinf hAsid]
  exact zero_le

/-! ## Formalized Decomposition & Multi-Octave Haar Sawtooth Variants from [Pa26] -/

/--
**Theorem 2.1(a) of [Pa26] (Harmonic-Difference Partial-Fraction Numerator Identity):**
For any positive integers $1 \le a_i < a_j$ with difference $d = a_j - a_i$,
$(d + 1) + (a_i - 1) = a_j$. Dividing by $(d + 1) a_j$ yields the exact identity
$\frac{1}{a_j} + \frac{a_i - 1}{(a_j - a_i + 1) a_j} = \frac{1}{a_j - a_i + 1}$
underlying the non-asymptotic Harmonic-Integral Conservation Law.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L35"]
theorem erdos_1191.variants.harmonic_conservation_numerator (a_i a_j d : ℕ)
    (h_pos : 1 ≤ a_i) (h_lt : a_i < a_j) (h_diff : d = a_j - a_i) :
    (d + 1) + (a_i - 1) = a_j := by
  sorry

/--
**Theorem 2.2(a) of [Pa26] (Two-Shell Inter-Shell Difference Localization):**
For $I_j = (2^{j-1}, 2^j]$ and $I_k = (2^{k-1}, 2^k]$ with $1 \le j \le k - 2$, any elements
$1 \le x \le 2^{k-2}$ and $2^{k-1} < y \le 2^k$ satisfy $2^{k-2} < y - x < 2^k$, so every
distant cross-shell difference lies in the two dyadic difference shells $D_{k-1} \cup D_k$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L50"]
theorem erdos_1191.variants.two_shell_difference_localization (x y pow_km2 : ℕ)
    (hx_pos : 1 ≤ x)
    (hx_hi : x ≤ pow_km2)
    (hy_lo : 2 * pow_km2 < y)
    (hy_hi : y ≤ 4 * pow_km2) :
    pow_km2 < y - x ∧ y - x < 4 * pow_km2 := by
  sorry

/--
Scaled bilinear sum for the powers-of-two Sidon set $A = \{2^n : n \ge 0\}$, where $m_k = 1$
and $A(2^{k-1}) = k$ for every $k \ge 1$. Multiplying $\sum_{k=1}^M \frac{2 m_k(m_k-1) + 2 m_k A(2^{k-1})}{2^k}$
by $2^M$ yields the integer sum $\sum_{k=1}^M k \cdot 2^{M - k + 1}$.
-/
def powersOfTwoScaledBilinear : ℕ → ℕ
  | 0 => 0
  | M + 1 => 2 * powersOfTwoScaledBilinear M + 2 * (M + 1)

/--
**Remark 2.3 of [Pa26] (Exact Closed-Form Bilinear Identity on $A = \{2^n : n \ge 0\}$):**
For every $M \ge 0$, the $2^M$-scaled bilinear sum on $A = \{2^n : n \ge 0\}$ satisfies the
exact closed-form identity $\bigl(\sum_{k=1}^M k \cdot 2^{M - k + 1}\bigr) + 2M + 4 = 2^{M + 2}$
(evaluating to $11/4 = 2.75$ at $M = 3$).
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L75"]
theorem erdos_1191.variants.powers_of_two_bilinear_identity (M : ℕ) :
    powersOfTwoScaledBilinear M + 2 * M + 4 = 2 ^ (M + 2) := by
  sorry

/--
**Theorem 2.2(b) & Remark 2.3 of [Pa26] (Verification of Corrected Bilinear Bound on $A = \{2^n : n \ge 0\}$):**
For every $M \ge 1$, the $2^M$-scaled bilinear sum on $A = \{2^n : n \ge 0\}$ is bounded above by
the $2^M$-scaled tight upper bound $(M + 1) 2^M - 2 = 2^M(M + 1 - 2^{-(M-1)})$ (certifying $22 \le 30$,
i.e., $11/4 \le 15/4$, at $M = 3$).
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L92"]
theorem erdos_1191.variants.powers_of_two_satisfies_corrected_bilinear_bound (M : ℕ) (hM : 1 ≤ M) :
    powersOfTwoScaledBilinear M ≤ (M + 1) * 2 ^ M - 2 := by
  sorry

/--
**Lemma 2.4 of [Pa26] (KKT Convex-Cone Increment Positivity for $k \ge 4$):**
For every shell index $k \ge 4$, $16 k^2 + 2(k^2 - 9) = 18(k^2 - 1)$ and $16 k^2 < 18(k^2 - 1)$.
Together with $9 > 8$ at $k = 3$, this certifies that the KKT multipliers $\lambda_k = 2^{1-k}(2\rho_k - \rho_{k+1})$
of the convex quadratic envelope program are strictly positive for all $k \ge 3$, so the cumulative
lower bound $A(2^k) \ge c\sqrt{2^k / \ln(2^k)}$ attains its unique global minimum on the boundary
$m_k^* = c \rho_k$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L115"]
theorem erdos_1191.variants.kkt_increment_convexity_k_ge_4 (k : ℕ) (hk : 4 ≤ k) :
    16 * (k * k) + 2 * (k * k - 9) = 18 * (k * k - 1) ∧
    16 * (k * k) < 18 * (k * k - 1) := by
  sorry

/--
**Theorem 2.5(b) & Theorem 2.11(c) of [Pa26] (Binary Sub-Block Variance Refinement Identity):**
Splitting a block of sum $S = S_1 + S_2$ into two equal sub-blocks satisfies
$2(S_1^2 + S_2^2) = (S_1 + S_2)^2 + (S_1 - S_2)^2 + (S_2 - S_1)^2$, so $2(S_1^2 + S_2^2) \ge (S_1 + S_2)^2$,
proving the monotone subadditivity refinement $L(S_1, B) + L(S_2, B) \ge L(S_1 + S_2, 2B)$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L132"]
theorem erdos_1191.variants.binary_subblock_variance_refinement (S1 S2 : ℕ) :
    2 * (S1 * S1 + S2 * S2) =
      (S1 + S2) * (S1 + S2) + (S1 - S2) * (S1 - S2) + (S2 - S1) * (S2 - S1) ∧
    (S1 + S2) * (S1 + S2) ≤ 2 * (S1 * S1 + S2 * S2) := by
  sorry

/--
**Theorem 2.6(a) of [Pa26] (Discrete Legendre–Fenchel Remainder Decomposition):**
For any bucket count $B \ge 1$ and total occupancy $S = B q + r$ with integer quotient $q$
and remainder $r \le B$, the minimum ordered-pair sum over $B$ integer buckets summing to $S$
satisfies $(B - r) q(q - 1) + r(q + 1) q = B q(q - 1) + 2 r q$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L220"]
theorem erdos_1191.variants.discrete_legendre_fenchel_excess (B q r : ℕ)
    (hr : r ≤ B) :
    (B - r) * (q * (q - 1)) + r * ((q + 1) * q) =
      B * (q * (q - 1)) + 2 * (r * q) := by
  sorry

/--
**Theorem 2.6(b) of [Pa26] (Squared-Total Discrete Legendre–Fenchel Integrality Identity):**
Multiplying the minimum ordered-pair count by $B$ yields the exact additive identity
$B(B q^2 + 2 r q) + B r = (B q + r)^2 + r(B - r)$, isolating the strictly non-negative
discrete integrality excess $r(B - r) = B^2 \theta(1 - \theta)$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L239"]
theorem erdos_1191.variants.legendre_fenchel_squared_identity (B q r : ℕ)
    (hr : r ≤ B) :
    B * (B * (q * q) + 2 * (r * q)) + B * r =
      (B * q + r) * (B * q + r) + r * (B - r) := by
  sorry

/--
**Theorem 2.6(c) of [Pa26] (Karamata Integer Convexity / Robin-Hood Smoothing Step):**
Whenever two sub-windows have occupancies $x_1 \ge x_2 + 2$, transferring one element from the
heavier window ($x_1 - 1$) to the lighter window ($x_2 + 1$) preserves the total occupancy and
strictly reduces the ordered-pair count $x_1(x_1 - 1) + x_2(x_2 - 1)$ by $2(x_1 - x_2 - 1) \ge 2$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L262"]
theorem erdos_1191.variants.robin_hood_pair_smoothing (x1 x2 : ℕ) (h_gap : x2 + 2 ≤ x1) :
    (x1 - 1) * (x1 - 2) + (x2 + 1) * x2 + 2 * (x1 - x2 - 1) =
      x1 * (x1 - 1) + x2 * (x2 - 1) := by
  sorry

/--
**Theorem 2.6(d) & Theorem 2.11(c) of [Pa26] (Exact Quarter-Square Sawtooth Ceiling & Relative Integrality Scaling):**
For any bucket count $B \ge 1$ and remainder $0 \le r \le B$, $4 r(B - r) + (2r - B)^2 + (B - 2r)^2 = B^2$,
so $4 r(B - r) \le B^2$ and the relative ratio of the integrality excess $r(B - r)$ to the leading
quadratic term $S^2$ is bounded above by $\frac{B^2}{4 S^2} = \frac{1}{4 \mu^2}$ where $\mu = S/B$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L293"]
theorem erdos_1191.variants.normalized_integrality_excess_bound (B r : ℕ) (hr : r ≤ B) :
    4 * (r * (B - r)) + (2 * r - B) * (2 * r - B) + (B - 2 * r) * (B - 2 * r) = B * B ∧
    4 * (r * (B - r)) ≤ B * B := by
  sorry

/--
**Theorem 2.7(a) of [Pa26] (Order-2 Cesàro–Fejér Triangular Kernel Step):**
For every $m \in \mathbb{N}$, $m(m - 1) + 2 m = (m + 1) m$, which gives the inductive step for
$$\sum_{w=1}^W (W + 1 - w)\max(w - |x - y|, 0) = \binom{W - d + 1}{2}$$
underlying the Order-2 Cesàro–Fejér window kernel in Theorems 2.7–2.11 of [Pa26].
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L362"]
theorem erdos_1191.variants.cesaro_fejer_order2_step (m : ℕ) :
    m * (m - 1) + 2 * m = (m + 1) * m := by
  sorry

/--
**Theorem 2.9(a) of [Pa26] (Scale-Invariant Block-Window Exponent Identity):**
For any shell index $k$, scale depth $s$, and octave offset $r$ with $1 \le s + r \le k$,
the sliding-window width exponent $k - (s + r)$ and sub-block count exponent $(s + r) - 1$
sum to $k - 1$ independently of $s$ and $r$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L378"]
theorem erdos_1191.variants.scale_invariant_block_window_exponents (k s r : ℕ)
    (hsr_pos : 1 ≤ s + r) (hsr_le : s + r ≤ k) :
    (k - (s + r)) + ((s + r) - 1) = k - 1 := by
  sorry

/--
**Theorem 2.9(b) of [Pa26] (Scale-Invariant Block-Window Product Identity):**
For any shell index $k$, scale depth $s$, and octave offset $r$ with $1 \le s + r \le k$,
the sliding-window width $w = 2^{k - s - r}$ and sub-block count $B = 2^{s + r - 1}$
satisfy $w \cdot B = 2^{k - 1} = |I_k|$ across all scales $s$ and octaves $r$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L389"]
theorem erdos_1191.variants.scale_invariant_block_window_product (k s r : ℕ)
    (hsr_pos : 1 ≤ s + r) (hsr_le : s + r ≤ k) :
    2 ^ (k - (s + r)) * 2 ^ ((s + r) - 1) = 2 ^ (k - 1) := by
  sorry

/--
**Theorem 2.11(b) of [Pa26] (Hyperfactorial Sawtooth Abel Coefficient Identity):**
For every integer period $m \ge 1$, $m(m + 1) - (m - 1)m = 2m$, telescoping the piecewise
logarithmic integrals of $\{u\}(1 - \{u\})/u$ into $2\ln H(M - 1)$ and the Glaisher–Kinkelin
sawtooth constant $C_{\mathrm{GK}} = 2\ln A_{\mathrm{GK}} = \frac{1}{6} - 2\zeta'(-1)$.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_1191/blob/main/Erdos1191/Proofs.lean#L403"]
theorem erdos_1191.variants.hyperfactorial_sawtooth_abel_step (m : ℕ) (hm : 1 ≤ m) :
    m * (m + 1) - (m - 1) * m = 2 * m := by
  sorry

/--
**Section 4 of [Pa26] (Bit-Reversed Shift Difference Identity):**
In a 64-bit register holding $\mathrm{rev\_mask} = \sum_{a \in A} 2^{63 - a}$, right-shifting by $63 - x$
places the bit for $a < x \le 63$ at bit position $(63 - a) - (63 - x) = x - a$.
-/
@[category API, AMS 5 11]
theorem erdos_1191.variants.bitshift_sidon_difference_index (a x : ℕ) (h_lt : a < x) (h_hi : x ≤ 63) :
    (63 - a) - (63 - x) = x - a := by
  omega

/-- All positive pairwise differences of a list of natural numbers. -/
def allPositiveDiffs : List ℕ → List ℕ
  | [] => []
  | a :: rest => (rest.map (fun b => b - a)) ++ allPositiveDiffs rest

/-- Boolean check that a list of natural numbers is strictly increasing. -/
def isStrictlyIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isStrictlyIncreasing (b :: rest)

/-- Boolean check that a list of natural numbers contains no duplicate entries. -/
def hasNoDuplicates : List ℕ → Bool
  | [] => true
  | d :: rest => !(rest.contains d) && hasNoDuplicates rest

/-- Boolean Sidon legality checker over a finite list of strictly increasing naturals. -/
def isCertifiedSidon (A : List ℕ) : Bool :=
  isStrictlyIncreasing A && hasNoDuplicates (allPositiveDiffs A)

/-- First 10 terms of the Mian–Chowla greedy Sidon sequence (OEIS `A005282`). -/
def mianChowlaPrefix10 : List ℕ := [1, 2, 4, 8, 13, 21, 31, 45, 66, 81]

/--
Machine-checked verification that the first 10 terms of the Mian–Chowla greedy sequence
$[1, 2, 4, 8, 13, 21, 31, 45, 66, 81]$ ([Pa26, Table 1], OEIS `A005282`) form a valid Sidon set
with $\binom{10}{2} = 45$ distinct positive differences.
-/
@[category test, AMS 5 11]
theorem mianChowlaPrefix10_is_sidon :
    isCertifiedSidon mianChowlaPrefix10 = true ∧
    (allPositiveDiffs mianChowlaPrefix10).length = 45 := by
  decide

/-- Optimal maximin lower-envelope Sidon witness $A^* = \{1, 2, 5, 7, 14, 22, 32\}$ at $N = 32$. -/
def maximinWitnessN32 : List ℕ := [1, 2, 5, 7, 14, 22, 32]

/--
Machine-checked verification that the maximin witness $A^* = [1, 2, 5, 7, 14, 22, 32]$ at $N = 32$
([Pa26, Table 2]) is a valid Sidon set with all $\binom{7}{2} = 21$ positive differences distinct.
-/
@[category test, AMS 5 11]
theorem maximinWitnessN32_is_sidon :
    isCertifiedSidon maximinWitnessN32 = true ∧
    (allPositiveDiffs maximinWitnessN32).length = 21 := by
  decide

end Erdos1191
