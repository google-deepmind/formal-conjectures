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

The three statements that need a long proof carry a `formal_proof` link to the version of this
file that contains it: the construction by runs, its counting function, and the growth estimate
behind `hasIntermediateGrowth_of_isGenuinelySublacunary`.

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

@[expose] public section

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

/- ## The counting function -/

/-- The counting function $\pi_A(N) = \#(A \cap [0, N])$ of the range $A$ of `m`. The outer
`Finset.range (N + 1)` is harmless for a strictly increasing `m`, since then $n \le m_n$. -/
def countingFn (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun n => m n ≤ N).card

/- ## Growth and sparsity alone are not a restriction -/

/-- **A lower bound on the size of the terms cannot make Problem 10.6 nontrivial.** For every
growth demand `f` there is a strictly increasing sequence dominating `f` at every index which
is dense modulo one for every irrational $\xi$.

In the subexponential range this is a special case of [Bos83, Thm. 1.5], which produces such a
sequence inside any prescribed corridor $[n_k, m_k)$ with $m_k - n_k \to \infty$ and
$m_k / n_k \to 1$, and in the stronger form of uniform distribution; the elementary
construction of the linked proof is uniform in `f` and has no growth ceiling. -/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/rwst/formal-conjectures/blob/63c3e7233f1e512ea2474f35f4f2cd70624583f6/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean#L398"]
theorem exists_dense_of_growth (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, f n ≤ m n) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  sorry

/-- **Neither can an upper bound on the counting function, even together with the growth
demand.** The same sequence dominates an arbitrary `f` *and* has counting function below
$(\log\log N)^2$ — an exponential below the $\log N$ floor that every sublacunary sequence
obeys, and so below the counting function of [Kat16, Cor. 4.10]. So a reading of "very rapidly
increasing" that constrains only the size of the terms or the sparsity of their range leaves
Problem 10.6 with no content. -/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/rwst/formal-conjectures/blob/63c3e7233f1e512ea2474f35f4f2cd70624583f6/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean#L411"]
theorem exists_dense_of_growth_and_sparsity (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, f n ≤ m n) ∧
      (∀ᶠ N : ℕ in atTop, (countingFn m N : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  sorry

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

/-- **A ratio floor implies intermediate growth**, at every exponent $\alpha < 1$. So the
ratio reading of Problem 10.6 is strictly stronger than the growth reading, and by
`exists_dense_of_growth` it is the reading that carries the content of the problem. -/
@[category API, AMS 11, formal_proof using formal_conjectures at
"https://github.com/rwst/formal-conjectures/blob/63c3e7233f1e512ea2474f35f4f2cd70624583f6/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean#L589"]
theorem hasIntermediateGrowth_of_isGenuinelySublacunary {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    HasIntermediateGrowth α m := by
  sorry

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
