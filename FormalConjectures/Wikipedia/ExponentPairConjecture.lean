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
# The exponent pair conjecture

Introduced by J. G. van der Corput (1922) and formalized systematically by E. Phillips (1933),
exponent-pair estimates bound exponential sums $\sum_{n=N}^{N'} e(f(n))$ whose phase $f$ has
derivatives on $[N, 2N]$ approximating those of a monomial with $f'(x) \approx y x^{-s}$
($y, s > 0$). Van der Corput's processes $A$ and $B$ generate new exponent pairs from $(0, 1)$, and
the **exponent pair conjecture** asserts that $(\varepsilon, 1/2 + \varepsilon)$ is an exponent
pair for every $\varepsilon \in (0, 1/2]$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Van_der_Corput%27s_method#Exponent_pairs)
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Number_theory)
- [vdC22] J. G. van der Corput, *Verschärfung der Abschätzung beim Teilerproblem*, Math. Ann. 87
  (1922), 39–65.
- [Ph33] E. Phillips, *The zeta-function of Riemann; further developments of van der Corput's
  method*, Quart. J. Math. Oxford 4 (1933), 209–225.
- [GK91] S. W. Graham and G. Kolesnik, *Van der Corput's Method of Exponential Sums*, London Math.
  Soc. Lecture Note Ser. 126, Cambridge Univ. Press, 1991, §3.3.
-/

@[expose] public section

namespace ExponentPairConjecture

open scoped ContDiff ExponentialSum

/-- The $(p + 1)$-th derivative $(-1)^p y \left(\prod_{j=0}^{p-1} (s + j)\right) x^{-(s + p)}$ of a
monomial phase whose first derivative is $y x^{-s}$. -/
noncomputable def modelMonomialDeriv (y s : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ p * y * (∏ j ∈ Finset.range p, (s + (j : ℝ))) * x ^ (-(s + (p : ℝ)))

/-- A $C^P$ function $f : \mathbb{R} \to \mathbb{R}$ is a *monomial-like phase of order $P$* on
$[N, 2N]$ with scale $y$, exponent $s$, and relative tolerance $\delta$ if its $(p + 1)$-th
derivative on $[N, 2N]$ lies within relative error $\delta$ of `modelMonomialDeriv y s p x` for all
$0 \le p < P$. -/
def IsMonomialPhase (f : ℝ → ℝ) (N P : ℕ) (y s δ : ℝ) : Prop :=
  ContDiff ℝ P f ∧
    ∀ p < P, ∀ x ∈ Set.Icc (N : ℝ) (2 * (N : ℝ)),
      |iteratedDeriv (p + 1) f x - modelMonomialDeriv y s p x| ≤
        δ * |modelMonomialDeriv y s p x|

/-- The finite exponential sum $\sum_{n = N}^{N'} e(f(n))$ with $e(t) = \exp(2\pi i t)$. -/
noncomputable def phaseExpSum (f : ℝ → ℝ) (N N' : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc N N', e (f (n : ℝ))

/-- A pair $(k, l)$ with $0 \le k \le 1/2 \le l \le 1$ is an *exponent pair* ([Ph33]; [GK91], §3.3)
if for every $s > 0$ there exist $P \ge 1$, $\delta > 0$, and $C > 0$ such that every order-$P$
monomial-like phase $f$ on $[N, 2N]$ ($N \ge 1$, $y > 0$) satisfies
$$\left|\sum_{n=N}^{N'} e(f(n))\right| \le C \max\bigl((y N^{-s})^k N^l,\, y^{-1} N^s\bigr)$$
for all $N \le N' \le 2N$.

Note: Following [Ph33] and [GK91], §3.3, the Kusmin–Landau term $y^{-1} N^s$ is included to cover
the non-oscillatory regime $y N^{-s} < 1$, which Wikipedia's informal summary omits. Bounding
dyadic prefix sums $\sum_{n=N}^{N'} e(f(n))$ ($N \le N' \le 2N$) agrees up to doubling $C$ with
bounding general subinterval sums $\sum_{n=a}^b e(f(n))$ ($N \le a \le b \le 2N$), and requiring
`ContDiff ℝ P f` on $\mathbb{R}$ matches $C^P([N, 2N])$ via smooth extension outside $[N, 2N]$. -/
def IsExponentPair (k l : ℝ) : Prop :=
  0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧
    ∀ s > 0, ∃ P : ℕ, 1 ≤ P ∧ ∃ δ > 0, ∃ C > 0,
      ∀ N N' : ℕ, 1 ≤ N → N ≤ N' → N' ≤ 2 * N →
        ∀ y > 0, ∀ f : ℝ → ℝ, IsMonomialPhase f N P y s δ →
          ‖phaseExpSum f N N'‖ ≤
            C * max ((y * (N : ℝ) ^ (-s)) ^ k * (N : ℝ) ^ l) (y⁻¹ * (N : ℝ) ^ s)

/-- At order $p = 0$, `modelMonomialDeriv y s 0 x` equals $y x^{-s}$. -/
@[category API, AMS 11 42]
theorem modelMonomialDeriv_zero (y s x : ℝ) :
    modelMonomialDeriv y s 0 x = y * x ^ (-s) := by
  simp [modelMonomialDeriv]

/-- Any constant phase satisfies `IsMonomialPhase` at scale $y = 0$. -/
@[category test, AMS 11 42]
theorem isMonomialPhase_const (c : ℝ) (N P : ℕ) (s δ : ℝ) :
    IsMonomialPhase (fun _ ↦ c) N P 0 s δ := by
  refine ⟨contDiff_const, fun p _ x _ ↦ ?_⟩
  simp [iteratedDeriv_const, modelMonomialDeriv]

/-- A linear phase $f(x) = y x$ satisfies `IsMonomialPhase` at order $P = 1$ and $s = 0$ for
$\delta \ge 0$. -/
@[category test, AMS 11 42]
theorem isMonomialPhase_linear (N : ℕ) (y : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMonomialPhase (fun x : ℝ ↦ y * x) N 1 y 0 δ := by
  refine ⟨contDiff_const.mul contDiff_id, fun p hp x _ ↦ ?_⟩
  obtain rfl : p = 0 := Nat.lt_one_iff.mp hp
  have hd : iteratedDeriv 1 (fun x : ℝ ↦ y * x) x = y := by
    rw [iteratedDeriv_one]
    simp
  rw [hd, modelMonomialDeriv_zero, neg_zero, Real.rpow_zero, mul_one, sub_self, abs_zero]
  exact mul_nonneg hδ (abs_nonneg y)

/-- Triangle inequality bound `‖phaseExpSum f N N'‖ ≤ 2 * N` for $1 \le N$ and $N' \le 2N$. -/
@[category API, AMS 11 42]
theorem norm_phaseExpSum_le_two_mul (f : ℝ → ℝ) {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N' ≤ 2 * N) :
    ‖phaseExpSum f N N'‖ ≤ 2 * (N : ℝ) := by
  calc
    ‖phaseExpSum f N N'‖
      ≤ ∑ n ∈ Finset.Icc N N', ‖e (f (n : ℝ))‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Icc N N', (1 : ℝ) := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [additiveChar, Complex.norm_exp_ofReal_mul_I]
    _ = ((Finset.Icc N N').card : ℝ) := by simp
    _ ≤ (2 * N : ℕ) := by
        exact_mod_cast (by rw [Nat.card_Icc]; omega : (Finset.Icc N N').card ≤ 2 * N)
    _ = 2 * (N : ℝ) := by push_cast; ring

/-- The trivial bound shows that $(0, 1)$ is an exponent pair. -/
@[category textbook, AMS 11 42]
theorem isExponentPair_zero_one : IsExponentPair 0 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun s _ ↦ ?_⟩
  refine ⟨1, le_rfl, 1, one_pos, 2, two_pos, fun N N' hN _ hNN' y _ f _ ↦ ?_⟩
  have htriv : ‖phaseExpSum f N N'‖ ≤ 2 * (N : ℝ) := norm_phaseExpSum_le_two_mul f hN hNN'
  have hmax : (N : ℝ) ≤ max ((y * (N : ℝ) ^ (-s)) ^ (0 : ℝ) * (N : ℝ) ^ (1 : ℝ))
      (y⁻¹ * (N : ℝ) ^ s) := by
    rw [Real.rpow_zero, one_mul, Real.rpow_one]
    exact le_max_left _ _
  linarith

/-- **Van der Corput's Process $A$** ([vdC22]; [Ph33]; [GK91], Theorem 3.6): Process $A$ maps any
exponent pair $(k, l)$ to the exponent pair
$\left(\frac{k}{2k + 2}, \frac{k + l + 1}{2k + 2}\right)$. -/
@[category research solved, AMS 11 42]
theorem isExponentPair_processA {k l : ℝ} (hkl : IsExponentPair k l) :
    IsExponentPair (k / (2 * k + 2)) ((k + l + 1) / (2 * k + 2)) := by
  sorry

/-- **Van der Corput's Process $B$** ([vdC22]; [Ph33]; [GK91], Theorem 3.7): Process $B$ maps any
exponent pair $(k, l)$ to the exponent pair $(l - 1 / 2, k + 1 / 2)$. -/
@[category research solved, AMS 11 42]
theorem isExponentPair_processB {k l : ℝ} (hkl : IsExponentPair k l) :
    IsExponentPair (l - 1 / 2) (k + 1 / 2) := by
  sorry

/-- **Exponent Pair Conjecture**: For every $\varepsilon \in (0, 1 / 2]$, the pair
$(\varepsilon, 1 / 2 + \varepsilon)$ is an exponent pair.

Note: The upper bound $\varepsilon \le 1 / 2$ ensures that $1 / 2 + \varepsilon \le 1$ lies in the
admissible exponent-pair interval $[1 / 2, 1]$. -/
@[category research open, AMS 11 42]
theorem exponent_pair_conjecture (ε : ℝ) (hε : ε ∈ Set.Ioc 0 (1 / 2)) :
    IsExponentPair ε (1 / 2 + ε) := by
  sorry

end ExponentPairConjecture
