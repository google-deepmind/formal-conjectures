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

import FormalConjecturesUtil

/-!
# Bugeaud Collection of Conjectures and Open Questions: Rapidly Increasing Sequences Dense Modulo One

Problem 10.6 asks for a "very rapidly increasing" sequence $(m_n)_{n \ge 1}$ of positive
integers with $(\{\xi m_n\})_{n \ge 1}$ dense modulo one for every irrational $\xi$. The
informal phrase admits several readings, and they are not equivalent:

* a lower bound on the size of the terms, $m_n \ge f(n)$;
* an upper bound on the counting function of $\{m_n\}$;
* a lower bound on the consecutive ratios, $m_{n+1}/m_n \ge 1 + c/\log n$.

The first two readings are vacuous, and `exists_dense_of_growth_and_sparsity` below says so: a
sequence built from runs of consecutive integers is dense modulo one for every irrational $\xi$
by an elementary argument, and the runs may be placed so that its terms dominate any prescribed
$f$ while its counting function stays below $(\log\log N)^2$. In the subexponential range the
growth half is a special case of [Bos83, Thm. 1.5], which produces such a sequence in any
prescribed subexponential corridor and in the stronger uniform-distribution form; the sparsity
half sits below the $\log N$ floor that every sublacunary sequence obeys, and so below the
counting function of [Kat16, Cor. 4.10]. Consequently `problem_10_6_variant_2`, which asks only
for intermediate growth, is not open.

The third reading is `IsGenuinelySublacunary`, and it is the only one with content: it implies
the first (`hasIntermediateGrowth_of_isGenuinelySublacunary`), and it is not answered by runs,
since inside a run $m_{n+1} - m_n = 1$. That reading is `problem_10_6_variant_1`, which remains
open; [Kat16, Cor. 4.9] gives a universally densifying sequence of multiplicative shape
$\{2^n 3^e\}$ whose ratio behaviour reduces the question to a Diophantine statement about
$\log_2 3$.

*References:*
  - [Bos83] Boshernitzan, Michael D. "Homogeneously distributed sequences and Poincaré sequences
    of integers of sublacunary growth." Monatshefte für Mathematik 96.3 (1983): 173-181.
  - [Bos94] Boshernitzan, Michael D. "Density modulo 1 of dilations of sublacunary sequences."
    Advances in Mathematics 108.1 (1994): 104-117.
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Fur67] Furstenberg, H. "Disjointness in ergodic theory, minimal sets, and a problem
    in diophantine approximation". Math. Systems Theory 1, 1–49 (1967).
  - [Kat16] Katz, Asaf. "Generalizations of Furstenberg's Diophantine result."
    arXiv:1607.00670 (2016).
  - [Mat80] de Mathan, Bernard. "Numbers contravening a condition in density modulo 1."
    Acta Mathematica Hungarica 36.3-4 (1980): 237-241.
  - [Pol79] Pollington, Andrew Douglas. "On the density of sequence $\{n_ {k}\xi\} $."
    Illinois Journal of Mathematics 23.4 (1979): 511-515.
-/

namespace Bugeaud06

open Filter

/- ## Two theorems from the literature -/

/-- The **Pollington–de Mathan theorem** [Pol79][Mat80]. For every lacunary sequence
$(m_n)_{n \ge 1}$ of positive integers, the set of real numbers $\xi$ for which
$(\{\xi m_n\})_{n \ge 1}$ is *not* dense modulo one has full Hausdorff dimension. -/
@[category research solved, AMS 11]
theorem pollington_de_mathan (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hlac : IsLacunary m) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 1 := by
  sorry

/-- The Pollington–de Mathan theorem implies that a lacunary sequence cannot answer
Problem 10.6. -/
@[category test, AMS 11]
theorem problem_lacunary_not_dense_of_pollington_de_mathan
    (h : type_of% pollington_de_mathan) :
    ∃ m : ℕ → ℕ, (∀ n, 0 < m n) ∧ IsLacunary m ∧
      ¬ ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  set m₀ : ℕ → ℕ := fun n => 2 ^ n with hm₀
  have hpos : ∀ n, 0 < m₀ n := by intro n; rw [hm₀]; positivity
  have hlac : IsLacunary m₀ := by
    refine ⟨3 / 2, by norm_num, .of_forall fun k => ?_⟩
    simp only [hm₀]
    push_cast [pow_succ]
    linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]
  refine ⟨m₀, hpos, hlac, fun hd => ?_⟩
  have hcount :
      {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m₀ n) : AddCircle (1 : ℝ)))}.Countable :=
    Set.Countable.mono (fun ξ hξ => by by_contra hξr; exact hξ (hd ξ hξr))
      (Set.countable_range _)
  exact zero_ne_one (hcount.dimH_zero ▸ h m₀ hpos hlac)

/-- **Furstenberg's theorem** [Fur67] (the $\times 2, \times 3$ case). For every irrational
number $\xi$, the two-parameter family $(\{\xi \, 2^m 3^n\})_{m, n \ge 1}$ is dense modulo
one. -/
@[category research solved, AMS 11]
theorem furstenberg_two_three (ξ : ℝ) (hξ : Irrational ξ) :
    Dense {x : AddCircle (1 : ℝ) |
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ x = ↑(ξ * (2 ^ m * 3 ^ n : ℕ))} := by
  sorry

/-- **Boshernitzan's theorem** [Bos94]. Given a real sublacunary sequence $r$, the set of
real numbers $\xi$ for which $(\{\xi r_n\})_{n \ge 1}$ is *not* dense modulo one has
Hausdorff dimension zero. -/
@[category research solved, AMS 11]
theorem boshernitzan (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hunb : ¬ BddAbove (Set.range r))
    (hsub : Tendsto (fun n => r (n + 1) / r n) atTop (nhds 1)) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * r n) : AddCircle (1 : ℝ)))} = 0 := by
  sorry

/- ## Sequences with arbitrarily long runs

A sequence containing arbitrarily long runs of consecutive integers is dense modulo one for
every irrational $\xi$. The point is that a run of length $L$ carries a translate of the
initial segment $\{j\xi : j \le L\}$ of the orbit of the rotation by $\xi$. -/

/-- A sequence `m` **has long runs** if for every `L` some window of `L + 1` consecutive
indices is mapped onto `L + 1` consecutive integers. Inside such a window
$m_{n+1} - m_n = 1$, which is the exact opposite of "rapidly increasing" locally. -/
def HasLongRuns (m : ℕ → ℕ) : Prop :=
  ∀ L : ℕ, ∃ a : ℕ, ∀ j ≤ L, m (a + j) = m a + j

/-- For irrational $\xi$ and every $\varepsilon > 0$ there is a bound `J` for which the
**initial segment** $\{j\xi : j \le J\}$ of the forward orbit is already $\varepsilon$-dense
in the circle.

The uniformity in `J` is what a run needs: a run has finite length, so a density statement
that returns an unbounded index is of no use. It comes from compactness of the circle. -/
@[category API, AMS 11]
theorem exists_bound_of_irrational (ξ : ℝ) (h : Irrational ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ c : AddCircle (1 : ℝ), ∃ j ≤ J, ‖(j • (ξ : AddCircle (1 : ℝ))) - c‖ < ε := by
  have hn : DenseRange (fun n : ℕ => (n • (ξ : AddCircle (1 : ℝ)))) :=
    denseRange_zsmul_iff_nsmul.1 (AddCircle.denseRange_zsmul_coe_iff.2 (by simpa using h))
  have hcover : (Set.univ : Set (AddCircle (1 : ℝ))) ⊆
      ⋃ j : ℕ, Metric.ball (j • (ξ : AddCircle (1 : ℝ))) ε := fun c _ => by
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hn c ε hε
    exact Set.mem_iUnion.2 ⟨j, by simpa [Metric.mem_ball, dist_comm] using hj⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun j : ℕ => Metric.isOpen_ball) hcover
  refine ⟨t.sup id, fun c => ?_⟩
  obtain ⟨j, hjt, hj⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ c))
  refine ⟨j, Finset.le_sup (f := id) hjt, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hj

/-- A sequence with arbitrarily long runs of consecutive integers is dense modulo one for
every irrational $\xi$.

Given `ξ`, a target `x` on the circle and `ε > 0`, take the bound `J` of
`exists_bound_of_irrational` and a run `m (a + j) = m a + j` of length at least `J`. The map
`j ↦ ξ m (a + j) = ξ m a + j ξ` is the initial segment `{j ξ : j ≤ J}` translated by `ξ m a`,
and a translation is an isometry of the circle, so the image meets the `ε`-ball around `x`. -/
@[category API, AMS 11]
theorem dense_of_hasLongRuns {m : ℕ → ℕ} (h : HasLongRuns m) (ξ : ℝ) (hξ : Irrational ξ) :
    Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨J, hJ⟩ := exists_bound_of_irrational ξ hξ hε
  obtain ⟨a, ha⟩ := h J
  obtain ⟨j, hjJ, hj⟩ := hJ (x - ((ξ * m a : ℝ) : AddCircle (1 : ℝ)))
  refine ⟨(↑(ξ * m (a + j)) : AddCircle (1 : ℝ)), ?_, ⟨a + j, rfl⟩⟩
  -- inside the run the orbit is the initial segment `{j ξ}` translated by `ξ m a`
  have hval : ((ξ * m (a + j) : ℝ) : AddCircle (1 : ℝ))
      = ((ξ * m a : ℝ) : AddCircle (1 : ℝ)) + j • ((ξ : ℝ) : AddCircle (1 : ℝ)) := by
    rw [ha j hjJ, show (ξ * ((m a + j : ℕ) : ℝ)) = ξ * m a + (j : ℕ) • ξ by
      push_cast [nsmul_eq_mul]; ring, AddCircle.coe_add, AddCircle.coe_nsmul]
  rw [Metric.mem_ball, dist_eq_norm, hval]
  convert hj using 2
  abel

/- ## A sequence of prescribed growth with long runs

The construction concatenates runs, the `k`-th of them of length `2 ^ k`, and pushes the value
at which run `k` starts above everything the growth demand `f` asks for on that run. The
dyadic indexing is what makes the block algebra free: `Nat.log 2` reads off the block. -/

/-- The dyadic block containing the position `n`: block `k` consists of the `2 ^ k` positions
with $2^k \le n + 1 < 2^{k+1}$. -/
def blockIdx (n : ℕ) : ℕ := Nat.log 2 (n + 1)

/-- The offset of the position `n` inside its block, so that `blockOff n < 2 ^ blockIdx n`. -/
def blockOff (n : ℕ) : ℕ := n + 1 - 2 ^ blockIdx n

/-- The largest value the growth demand `f` takes on block `k` or below. Taking a supremum
rather than the single value `f k` is what lets the growth statement hold for an **arbitrary**
`f`: dominating `f` at one index per block would need `f` to be monotone. -/
def growthSup (f : ℕ → ℕ) (k : ℕ) : ℕ := (Finset.range (2 ^ (k + 1))).sup f

/-- The tower forced into the block starts to make the counting function small: block `k`
starts beyond $2^{2^{4^k}}$, so that the $2^{k+1}$ terms produced up to that point are counted
against a very large $N$. -/
def sparsityTower (k : ℕ) : ℕ := 2 ^ (2 ^ (4 ^ k))

/-- The value at which block `k` starts. The `max` encodes the three demands: room for the
previous block (`+ 2 ^ k`, which is what keeps the sequence strictly increasing across a block
boundary), the growth demand `f`, and the sparsity tower. -/
def blockStart (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => max (growthSup f 0) (sparsityTower 0) + 1
  | k + 1 => max (blockStart f k + 2 ^ k) (max (growthSup f (k + 1)) (sparsityTower (k + 1))) + 1

/-- **The sequence.** Inside block `k` it runs through the `2 ^ k` consecutive integers starting
at `blockStart f k`. -/
def runSeq (f : ℕ → ℕ) (n : ℕ) : ℕ := blockStart f (blockIdx n) + blockOff n

@[category API, AMS 11]
theorem pow_blockIdx_le (n : ℕ) : 2 ^ blockIdx n ≤ n + 1 :=
  Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)

@[category API, AMS 11]
theorem lt_pow_blockIdx_succ (n : ℕ) : n + 1 < 2 ^ (blockIdx n + 1) :=
  Nat.lt_pow_succ_log_self Nat.one_lt_two _

@[category API, AMS 11]
theorem blockOff_lt (n : ℕ) : blockOff n < 2 ^ blockIdx n := by
  have h2 := lt_pow_blockIdx_succ n
  rw [pow_succ] at h2
  show n + 1 - 2 ^ blockIdx n < 2 ^ blockIdx n
  omega

@[category API, AMS 11]
theorem blockIdx_mono : Monotone blockIdx := fun _ _ h => Nat.log_mono_right (Nat.succ_le_succ h)

/-- The positions of block `k` are `2 ^ k - 1 + j` for `j < 2 ^ k`. -/
@[category API, AMS 11]
theorem blockIdx_run (k j : ℕ) (hj : j < 2 ^ k) : blockIdx (2 ^ k - 1 + j) = k := by
  show Nat.log 2 (2 ^ k - 1 + j + 1) = k
  rw [show 2 ^ k - 1 + j + 1 = 2 ^ k + j by omega]
  exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)

@[category API, AMS 11]
theorem blockOff_run (k j : ℕ) (hj : j < 2 ^ k) : blockOff (2 ^ k - 1 + j) = j := by
  simp only [blockOff, blockIdx_run k j hj]
  omega

@[category API, AMS 11]
theorem blockStart_lt_succ (f : ℕ → ℕ) (k : ℕ) :
    blockStart f k + 2 ^ k < blockStart f (k + 1) :=
  Nat.lt_succ_of_le (le_max_left _ _)

@[category API, AMS 11]
theorem blockStart_strictMono (f : ℕ → ℕ) : StrictMono (blockStart f) :=
  strictMono_nat_of_lt_succ fun k => (Nat.le_add_right _ _).trans_lt (blockStart_lt_succ f k)

@[category API, AMS 11]
theorem growthSup_le_blockStart (f : ℕ → ℕ) (k : ℕ) : growthSup f k ≤ blockStart f k := by
  cases k with
  | zero => exact Nat.le_succ_of_le (le_max_left _ _)
  | succ k => exact Nat.le_succ_of_le ((le_max_left _ _).trans (le_max_right _ _))

@[category API, AMS 11]
theorem sparsityTower_le_blockStart (f : ℕ → ℕ) (k : ℕ) : sparsityTower k ≤ blockStart f k := by
  cases k with
  | zero => exact Nat.le_succ_of_le (le_max_right _ _)
  | succ k => exact Nat.le_succ_of_le ((le_max_right _ _).trans (le_max_right _ _))

@[category API, AMS 11]
theorem runSeq_run (f : ℕ → ℕ) (k j : ℕ) (hj : j < 2 ^ k) :
    runSeq f (2 ^ k - 1 + j) = blockStart f k + j := by
  simp only [runSeq, blockIdx_run k j hj, blockOff_run k j hj]

/-- The sequence is strictly increasing: inside a block it steps by one, and across a boundary
the gap `blockStart f (k + 1) - (blockStart f k + 2 ^ k) > 0` is what the recursion provides. -/
@[category API, AMS 11]
theorem runSeq_strictMono (f : ℕ → ℕ) : StrictMono (runSeq f) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hle : blockIdx n ≤ blockIdx (n + 1) := blockIdx_mono (Nat.le_succ n)
  simp only [runSeq]
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- inside a block the offset steps by one
    simp only [blockOff]
    rw [← heq]
    have := pow_blockIdx_le n
    omega
  · -- across a boundary the recursion has left room
    have h1 := blockOff_lt n
    have h2 := blockStart_lt_succ f (blockIdx n)
    have h3 : blockStart f (blockIdx n + 1) ≤ blockStart f (blockIdx (n + 1)) :=
      (blockStart_strictMono f).monotone hlt
    omega

/-- **The runs.** Block `k` is a run of `2 ^ k` consecutive integers, so runs of every length
occur. -/
@[category API, AMS 11]
theorem runSeq_hasLongRuns (f : ℕ → ℕ) : HasLongRuns (runSeq f) := by
  intro L
  refine ⟨2 ^ (L + 1) - 1, fun j hj => ?_⟩
  have hj' : j < 2 ^ (L + 1) :=
    hj.trans_lt (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ L)))
  have hstart : runSeq f (2 ^ (L + 1) - 1) = blockStart f (L + 1) := by
    simpa using runSeq_run f (L + 1) 0 (Nat.two_pow_pos _)
  rw [runSeq_run f (L + 1) j hj', hstart]

/-- **The growth.** The sequence dominates an arbitrary prescribed `f` at *every* index; no
monotonicity of `f` is assumed and no bound on how fast it grows. -/
@[category API, AMS 11]
theorem le_runSeq (f : ℕ → ℕ) (n : ℕ) : f n ≤ runSeq f n := by
  have h1 : f n ≤ growthSup f (blockIdx n) :=
    Finset.le_sup (Finset.mem_range.2 (Nat.lt_of_succ_lt (lt_pow_blockIdx_succ n)))
  have h2 := growthSup_le_blockStart f (blockIdx n)
  show f n ≤ blockStart f (blockIdx n) + blockOff n
  omega

/- ## The counting function -/

/-- The counting function $\pi_A(N) = \#(A \cap [0, N])$ of the range $A$ of `m`. The outer
`Finset.range (N + 1)` is harmless for a strictly increasing `m`, since then $n \le m_n$. -/
def countingFn (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun n => m n ≤ N).card

/-- The counting function of a strictly increasing sequence is bounded by any index whose value
already exceeds `N`: $\pi_A(N) \le M$ as soon as $m_M > N$. This is the only property of
`countingFn` used below, and it is why a sparsity bound is a growth statement in disguise. -/
@[category API, AMS 11]
theorem countingFn_le {m : ℕ → ℕ} (hm : StrictMono m) {N M : ℕ} (h : N < m M) :
    countingFn m N ≤ M := by
  have hsub : ((Finset.range (N + 1)).filter fun n => m n ≤ N) ⊆ Finset.range M := fun n hn => by
    rw [Finset.mem_filter] at hn
    -- `m n ≤ N < m M`, and `m` is strictly increasing
    exact Finset.mem_range.2 (hm.lt_iff_lt.1 (hn.2.trans_lt h))
  show ((Finset.range (N + 1)).filter fun n => m n ≤ N).card ≤ M
  simpa using Finset.card_le_card hsub

@[category API, AMS 11]
theorem runSeq_at_blockStart (f : ℕ → ℕ) (k : ℕ) :
    runSeq f (2 ^ k - 1) = blockStart f k := by
  simpa using runSeq_run f k 0 (Nat.two_pow_pos k)

/-- Below the start of block `k` the sequence has produced at most `2 ^ k - 1` terms. -/
@[category API, AMS 11]
theorem countingFn_le_of_lt_blockStart (f : ℕ → ℕ) {N k : ℕ} (h : N < blockStart f k) :
    countingFn (runSeq f) N ≤ 2 ^ k - 1 :=
  countingFn_le (runSeq_strictMono f) (by rw [runSeq_at_blockStart]; exact h)

/-- **The sparsity.** The counting function of the construction stays below
$(\log\log N)^2$. The mechanism is the tower in `blockStart`: at the moment block $k$ opens,
only $2^{k+1}$ terms have been produced, while every term already exceeds $2^{2^{4^{k-1}}}$,
so two peels of the logarithm leave $4^{k-1}$ against a count of $2^{k+1}$. -/
@[category API, AMS 11]
theorem runSeq_countingFn_le (f : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop, (countingFn (runSeq f) N : ℝ) ≤ (Real.log (Real.log N)) ^ 2 := by
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
  refine Filter.eventually_atTop.2 ⟨blockStart f 2, fun N hN => ?_⟩
  -- the least block start exceeding `N`; it is `j + 1` with `2 ≤ j`
  have hex : ∃ k, N < blockStart f k :=
    ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N) (blockStart_strictMono f).le_apply⟩
  have hk : N < blockStart f (Nat.find hex) := Nat.find_spec hex
  have hk3 : 3 ≤ Nat.find hex := by
    by_contra hcon
    exact absurd (hk.trans_le ((blockStart_strictMono f).monotone (show Nat.find hex ≤ 2 by omega)))
      (by omega)
  obtain ⟨j, hj2, hj⟩ : ∃ j, 2 ≤ j ∧ Nat.find hex = j + 1 :=
    ⟨Nat.find hex - 1, by omega, by omega⟩
  have hcount : countingFn (runSeq f) N ≤ 2 ^ (j + 1) := by
    have := countingFn_le_of_lt_blockStart f (hj ▸ hk)
    have := Nat.two_pow_pos (j + 1)
    omega
  -- the size of `N`, and two peels of the logarithm
  have hNbig : ((2 : ℝ)) ^ (2 ^ (4 ^ j)) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (sparsityTower_le_blockStart f j)
      (Nat.not_lt.1 (Nat.find_min hex (by omega)))
  have hlogN : ((2 : ℝ) ^ (4 ^ j)) * Real.log 2 ≤ Real.log N := by
    simpa [Real.log_pow] using Real.log_le_log (by positivity) hNbig
  have hloglog : (((4 : ℝ) ^ j) - 1) * Real.log 2 ≤ Real.log (Real.log N) := by
    have hhalf : (2 : ℝ) ^ (4 ^ j) / 2 ≤ Real.log N := by
      nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (4 ^ j) by positivity]
    have h := Real.log_le_log (show (0 : ℝ) < (2 : ℝ) ^ (4 ^ j) / 2 by positivity) hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
    push_cast at h
    linarith
  -- the elementary estimate `2 ^ (j + 1) ≤ (2 ^ j) ^ 2 ≤ ((4 ^ j - 1) * log 2) ^ 2` for `j ≥ 2`
  have ht : (4 : ℝ) ≤ (2 : ℝ) ^ j := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact pow_le_pow_right₀ one_le_two hj2
  have hsq : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hkey : (2 : ℝ) ^ j ≤ (((4 : ℝ) ^ j) - 1) * Real.log 2 := by
    rw [← hsq]; nlinarith [sq_nonneg ((2 : ℝ) ^ j - 4)]
  calc (countingFn (runSeq f) N : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast hcount
    _ ≤ ((2 : ℝ) ^ j) ^ 2 := by rw [pow_succ]; nlinarith
    _ ≤ (Real.log (Real.log N)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hkey.trans hloglog) 2

/- ## Growth and sparsity alone are not a restriction -/

/-- **A lower bound on the size of the terms cannot make Problem 10.6 nontrivial.** For every
growth demand `f` there is a strictly increasing sequence dominating `f` at every index which
is dense modulo one for every irrational $\xi$.

In the subexponential range this is a special case of [Bos83, Thm. 1.5], which produces such a
sequence inside any prescribed corridor $[n_k, m_k)$ with $m_k - n_k \to \infty$ and
$m_k / n_k \to 1$, and in the stronger form of uniform distribution; the elementary
construction here is uniform in `f` and has no growth ceiling. -/
@[category research solved, AMS 11]
theorem exists_dense_of_growth (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, f n ≤ m n) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  ⟨runSeq f, runSeq_strictMono f, le_runSeq f, dense_of_hasLongRuns (runSeq_hasLongRuns f)⟩

/-- **Neither can an upper bound on the counting function, even together with the growth
demand.** The same sequence dominates an arbitrary `f` *and* has counting function below
$(\log\log N)^2$ — an exponential below the $\log N$ floor that every sublacunary sequence
obeys, and so below the counting function of [Kat16, Cor. 4.10]. So a reading of "very rapidly
increasing" that constrains only the size of the terms or the sparsity of their range leaves
Problem 10.6 with no content. -/
@[category research solved, AMS 11]
theorem exists_dense_of_growth_and_sparsity (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, f n ≤ m n) ∧
      (∀ᶠ N : ℕ in atTop, (countingFn m N : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  ⟨runSeq f, runSeq_strictMono f, le_runSeq f, runSeq_countingFn_le f,
    dense_of_hasLongRuns (runSeq_hasLongRuns f)⟩

/- ## The ratio-floor reading -/

/-- The sequence defined by $m_0 = 2$ and $m_{n+1} = \lceil m_n (1 + 1/\log n) \rceil$. -/
noncomputable def mSeq : ℕ → ℕ
  | 0 => 2
  | (n + 1) => ⌈(mSeq n : ℝ) * (1 + 1 / Real.log n)⌉₊

/-- The sequence $m$ eventually grows at least geometrically with a logarithmic correction. -/
def IsGenuinelySublacunary (m : ℕ → ℕ) : Prop :=
  ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, (1 + c / Real.log n) ≤ (m (n+1) : ℝ) / m n

/-- The sequence `mSeq`, given by $m_{n+1} = \lceil m_n (1 + 1/\log n) \rceil$, is
genuinely sublacunary: taking $c = 1$, we have $m_{n+1}/m_n \ge 1 + 1/\log n$ because
$\lceil m_n (1 + 1/\log n) \rceil \ge m_n (1 + 1/\log n)$. -/
@[category test, AMS 11]
lemma example_isGenuineSublacunary : IsGenuinelySublacunary mSeq := by
  -- Every term of `mSeq` is positive.
  have mSeq_pos : ∀ n, 0 < mSeq n := fun n => by
    induction n with
    | zero => simp [mSeq]
    | succ k ih =>
      simp only [mSeq, Nat.ceil_pos]
      exact mul_pos (by exact_mod_cast ih) (by positivity)
  refine ⟨1, one_pos, .of_forall fun n => ?_⟩
  have hpos : (0 : ℝ) < (mSeq n : ℝ) := by exact_mod_cast mSeq_pos n
  rw [le_div_iff₀ hpos, mul_comm]
  simp only [mSeq]
  exact Nat.le_ceil _

/-- A ratio floor is weaker than lacunarity: a lacunary sequence has ratios bounded below by a
constant $> 1$, which dominates $1 + c/\log n$. So `IsGenuinelySublacunary` is a floor under
the ratios, not a denial of lacunarity. -/
@[category API, AMS 11]
theorem isGenuinelySublacunary_of_isLacunary {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n)
    (h : IsLacunary m) : IsGenuinelySublacunary m := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨c - 1, by linarith, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 3] with n hn hn3
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hpn : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos n
  have hlog : (1 : ℝ) ≤ Real.log n :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have hdiv : (c - 1) / Real.log n ≤ c - 1 := div_le_self (by linarith) hlog
  rw [le_div_iff₀ hpn]
  nlinarith

/-- The sequence $m$ eventually grows at least as fast as $\exp(n^{\alpha})$, i.e., super-exponential
growth when $\alpha > 1$, and stretched-exponential when $0 < \alpha < 1$. -/
def HasIntermediateGrowth (α : ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ᶠ (n : ℕ) in atTop, Real.exp ((n : ℝ) ^ α) ≤ m n

/- ### A ratio floor forces intermediate growth

The chain below proves `hasIntermediateGrowth_of_isGenuinelySublacunary`: a ratio floor
$1 + c/\log n$ forces $\log m_n \ge (c/4) \, n / \log n$, which beats $n^\alpha$ for every
$\alpha < 1$. It is what makes the ratio reading strictly stronger than the growth reading. -/

/-- `log n = o(nʳ)`, in the shape the growth estimate uses. -/
@[category API, AMS 11]
theorem eventually_log_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ (n : ℕ) in atTop, Real.log n ≤ c * (n : ℝ) ^ r := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_atTop hr).def hc), Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1R),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) r)] at hn

/-- `log n → ∞` along the naturals. -/
@[category API, AMS 11]
theorem tendsto_log_natCast : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- A sequence with a ratio floor is eventually positive: a ratio with a zero denominator is
`0` in Lean's convention, which the floor `1 + c/\log n > 0` excludes. -/
@[category API, AMS 11]
theorem eventually_pos_of_isGenuinelySublacunary {m : ℕ → ℕ} (h : IsGenuinelySublacunary m) :
    ∀ᶠ n : ℕ in atTop, 0 < m n := by
  obtain ⟨c, hc, hev⟩ := h
  filter_upwards [hev, eventually_ge_atTop 3] with n hn hn3
  by_contra hcon
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  rw [show m n = 0 by omega, Nat.cast_zero, div_zero] at hn
  linarith [div_pos hc (Real.log_pos (by linarith : (1 : ℝ) < (n : ℝ)))]

/-- The per-step increment of $\log m_n$: from $1 + c/\log n \le m_{n+1}/m_n$ and
$\log(1 + x) \ge x/(1+x)$, with $x = c/\log n \le 1$ so that $1 + x \le 2$. -/
@[category API, AMS 11]
theorem log_step_of_isGenuinelySublacunary {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hev : ∀ᶠ n : ℕ in atTop, (1 + c / Real.log n) ≤ (m (n + 1) : ℝ) / m n) :
    ∀ᶠ n : ℕ in atTop, c / (2 * Real.log n) ≤ Real.log (m (n + 1)) - Real.log (m n) := by
  filter_upwards [hev, tendsto_log_natCast.eventually_ge_atTop c,
    tendsto_log_natCast.eventually_ge_atTop 1] with n hn hcn h1n
  have hlogpos : (0 : ℝ) < Real.log n := by linarith
  set x : ℝ := c / Real.log n with hx
  have hx0 : 0 < x := div_pos hc hlogpos
  have hx1 : x ≤ 1 := by rw [hx]; exact (div_le_one hlogpos).2 hcn
  -- the floor `1 + x > 0` rules out a vanishing numerator or denominator
  have hmn : (0 : ℝ) < (m n : ℝ) := by
    rcases Nat.eq_zero_or_pos (m n) with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero] at hn; linarith
    · exact_mod_cast h0
  have hmn' : (0 : ℝ) < (m (n + 1) : ℝ) := by
    rcases Nat.eq_zero_or_pos (m (n + 1)) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_div] at hn; linarith
    · exact_mod_cast h0
  have hlogdiv : Real.log (1 + x) ≤ Real.log (m (n + 1)) - Real.log (m n) := by
    have h := Real.log_le_log (by linarith) hn
    rwa [Real.log_div (ne_of_gt hmn') (ne_of_gt hmn)] at h
  -- `log (1 + x) ≥ 1 - (1 + x)⁻¹ = x / (1 + x) ≥ x / 2`, since `x ≤ 1`
  have hkey : x / 2 ≤ Real.log (1 + x) := by
    have h1 : (1 + x)⁻¹ ≤ 1 - x / 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; nlinarith
    linarith [Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + x by linarith)]
  have hrw : c / (2 * Real.log n) = x / 2 := by rw [hx]; ring
  linarith

/-- The summed form, by induction and with no finite sums: the denominator $\log(N + j)$ is
monotone in `j`, so the accumulated bound may be carried at the current denominator throughout. -/
@[category API, AMS 11]
theorem log_lower_aux {m : ℕ → ℕ} {c : ℝ} {N : ℕ} (hc : 0 < c) (hN : 3 ≤ N)
    (hstep : ∀ n, N ≤ n → c / (2 * Real.log n) ≤ Real.log (m (n + 1)) - Real.log (m n))
    (hbase : 0 ≤ Real.log (m N)) :
    ∀ j : ℕ, (j : ℝ) * (c / (2 * Real.log ((N + j : ℕ) : ℝ))) ≤ Real.log (m (N + j)) := by
  intro j
  induction j with
  | zero => simpa using hbase
  | succ i ih =>
    have ha3 : (3 : ℝ) ≤ ((N + i : ℕ) : ℝ) := by exact_mod_cast show 3 ≤ N + i by omega
    have hpos : (0 : ℝ) < Real.log ((N + i : ℕ) : ℝ) := Real.log_pos (by linarith)
    -- the denominator only grows, so the accumulated bound may be carried at the new one
    have hle : Real.log ((N + i : ℕ) : ℝ) ≤ Real.log ((N + i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (Nat.cast_le.2 (Nat.le_succ _))
    have hmono : c / (2 * Real.log ((N + i + 1 : ℕ) : ℝ))
        ≤ c / (2 * Real.log ((N + i : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have h1 := hstep (N + i) (by omega)
    have h2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)
    rw [show N + (i + 1) = N + i + 1 by omega, Nat.cast_add_one i]
    linarith

/-- **The growth estimate.** A ratio floor $1 + c/\log n$ forces
$\log m_n \ge (c/4) \, n/\log n$ eventually. The constant is deliberately loose: both halves
of the factor `4` come from harmless slack (`log(1+x) ≥ x/2` and `n - N ≥ n/2`). -/
@[category API, AMS 11]
theorem log_lower_of_isGenuinelySublacunary {m : ℕ → ℕ} (h : IsGenuinelySublacunary m) :
    ∃ c' > 0, ∀ᶠ n : ℕ in atTop, c' * n / Real.log n ≤ Real.log (m n) := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨c / 4, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((log_step_of_isGenuinelySublacunary hc hev).and
      (eventually_pos_of_isGenuinelySublacunary ⟨c, hc, hev⟩)).and (eventually_ge_atTop 3))
  have hN3 : 3 ≤ N := (hN N le_rfl).2
  have hbase : 0 ≤ Real.log (m N) := Real.log_nonneg (by exact_mod_cast (hN N le_rfl).1.2)
  have haux := log_lower_aux hc hN3 (fun n hn => (hN n hn).1.1) hbase
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  -- at index `n` the summed bound has accumulated `n - N ≥ n / 2` steps
  have hj := haux (n - N)
  rw [show N + (n - N) = n by omega, Nat.cast_sub (by omega : N ≤ n)] at hj
  have hnR : (2 * N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast show 1 < n by omega)
  calc c / 4 * n / Real.log n = ((n : ℝ) / 2) * (c / (2 * Real.log n)) := by
        field_simp; ring
    _ ≤ ((n : ℝ) - N) * (c / (2 * Real.log n)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ Real.log (m n) := hj

/-- **A ratio floor implies intermediate growth**, at every exponent $\alpha < 1$. So the
ratio reading of Problem 10.6 is strictly stronger than the growth reading, and by
`exists_dense_of_growth` it is the reading that carries the content of the problem. -/
@[category API, AMS 11]
theorem hasIntermediateGrowth_of_isGenuinelySublacunary {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    HasIntermediateGrowth α m := by
  obtain ⟨c', hc', hlow⟩ := log_lower_of_isGenuinelySublacunary h
  filter_upwards [hlow, eventually_log_le (c := c') (r := 1 - α) hc' (by linarith),
    eventually_pos_of_isGenuinelySublacunary h, eventually_ge_atTop 3] with n hn hlog hpos hn3
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hmpos : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos
  rw [← Real.exp_log hmpos]
  refine Real.exp_le_exp.2 ((le_div_iff₀ hlogpos).2 ?_ |>.trans hn)
  calc (n : ℝ) ^ α * Real.log n ≤ (n : ℝ) ^ α * (c' * (n : ℝ) ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnpos.le α)
    _ = c' * ((n : ℝ) ^ α * (n : ℝ) ^ (1 - α)) := by ring
    _ = c' * n := by rw [← Real.rpow_add hnpos]; simp

/-- `mSeq` has intermediate (subexponential but super-polynomial) growth: for every
`0 < α < 1` its terms eventually dominate $\exp(n^\alpha)$. This is the ratio floor of
`example_isGenuineSublacunary` fed into
`hasIntermediateGrowth_of_isGenuinelySublacunary`. -/
@[category test, AMS 11]
lemma example_hasIntermediateGrowth (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    HasIntermediateGrowth α mSeq :=
  hasIntermediateGrowth_of_isGenuinelySublacunary example_isGenuineSublacunary hα₀ hα₁

/-- A sequence that is dense modulo one for every irrational $\xi$ cannot be lacunary: its
exceptional set is contained in $\mathbb{Q}$, hence countable and of Hausdorff dimension zero,
whereas `pollington_de_mathan` gives dimension one for a lacunary sequence. So an answer to
Problem 10.6 under the ratio reading is pinched: the ratios must return to $1$ along a
subsequence, and yet stay above $1 + c/\log n$ eventually. The two are compatible only because
$c/\log n \to 0$. -/
@[category test, AMS 11]
theorem not_isLacunary_of_dense (h : type_of% pollington_de_mathan) {m : ℕ → ℕ}
    (hpos : ∀ n, 0 < m n)
    (hdense : ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))) :
    ¬ IsLacunary m := by
  intro hlac
  have hcount :
      {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))}.Countable :=
    Set.Countable.mono (fun ξ hξ => by by_contra hξr; exact hξ (hdense ξ hξr))
      (Set.countable_range _)
  exact zero_ne_one (hcount.dimH_zero ▸ h m hpos hlac)

/- ## The problem -/

/--
Problem 10.6. Find a very rapidly increasing sequence $(m_n)_{n \ge 1}$ of positive
integers such that $(\{\xi m_n\})_{n \ge 1}$ is dense modulo one for every irrational
number $\xi$. Note: Furstenberg's $2^m3^n$ is sublacunary but requires two parameters.

This is the reading of "very rapidly increasing" as a lower bound on the consecutive ratios,
and it is the one that remains open. It is not answered by runs of consecutive integers, since
inside a run $m_{n+1} - m_n = 1$; and by `not_isLacunary_of_dense` any answer is pinched
between a decaying ratio floor and the failure of lacunarity. [Kat16, Cor. 4.9] gives a
universally densifying sequence of the multiplicative shape $\{2^n 3^e\}$, for which the
ratio condition reduces to a Diophantine statement about the differences of the exponents
$e$ times $\log_2 3$ modulo one.
-/
@[category research open, AMS 11]
theorem problem_10_6_variant_1 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    IsGenuinelySublacunary m ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  sorry

/-- Problem 10.6, intermediate-growth variant. This asks only for a lower bound on the size of
the terms, and under that reading the problem is not open: runs of consecutive integers answer
it, by `exists_dense_of_growth` applied to $f(n) = \lceil e^n \rceil$. The witness below is
exhibited at $\alpha = 1/2$; the same sequence works for every $\alpha < 1$, since
$\exp(n^\alpha) \le \exp(n) \le f(n)$ there.

The result is not new: [Bos83, Thm. 1.5] gives a sequence of any prescribed subexponential
growth that is uniformly distributed — not merely dense — modulo one for every irrational
dilate. -/
@[category research solved, AMS 11]
theorem problem_10_6_variant_2 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ HasIntermediateGrowth α m) ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  obtain ⟨m, hmono, hgrow, hdense⟩ := exists_dense_of_growth (fun n => ⌈Real.exp n⌉₊)
  refine ⟨m, hmono, ⟨1 / 2, by norm_num, by norm_num, ?_⟩, hdense⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc Real.exp (((n : ℝ)) ^ (1 / 2 : ℝ)) ≤ Real.exp (((n : ℝ)) ^ (1 : ℝ)) :=
        Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
    _ = Real.exp n := by rw [Real.rpow_one]
    _ ≤ ((⌈Real.exp n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    _ ≤ ((m n : ℕ) : ℝ) := by exact_mod_cast hgrow n

end Bugeaud06
