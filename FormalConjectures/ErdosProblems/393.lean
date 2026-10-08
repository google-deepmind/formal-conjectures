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
public import FormalConjectures.Wikipedia.ABC

/-!
# Erdős Problem 393

*References:*
- [erdosproblems.com/393](https://www.erdosproblems.com/393)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [BeOs92] Berend, Daniel and Osgood, Charles F., *On the equation $P(x)=n!$ and a question of
  Erdős*. J. Number Theory 42 (1992), 189-193.
- [BPZ23] Bui, Hung M. and Pratt, Kyle and Zaharescu, Alexandru, *Power savings for counting
  solutions to polynomial-factorial equations*. Adv. Math. 422 (2023), Paper No. 109021, 32 pp.
  [arXiv:2204.08423](https://arxiv.org/abs/2204.08423)
- [Lu02] Luca, Florian, *The Diophantine equation $P(x)=n!$ and a result of M. Overholt*.
  Glas. Mat. Ser. III 37 (2002), 269-273.
- [OEIS A388302](https://oeis.org/A388302): the values $f(n)$ for $n \geq 2$.
- [Adapted proofs](https://github.com/google-deepmind/formal-conjectures/pull/6860),
  veljjanoski, commit `64c94684e6b82d0b88065ab7b5d1d3201760de3f`.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace Erdos393

/-- Distinct factors of `n!` with exact positive diameter `m`.
Both endpoints are used. Interior integers may be omitted. Positivity of every
factor follows from the nonzero factorial product. -/
def HasWidth (n m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ a : ℕ, ∃ s : Finset ℕ, s ⊆ Finset.Icc a (a + m) ∧
    a ∈ s ∧ a + m ∈ s ∧ s.prod id = n.factorial

/-- The minimum positive width. For `n=0,1` the admissible set is empty and
the value is `0`. The source's intended domain is `n ≥ 2`. -/
noncomputable def f (n : ℕ) : ℕ := sInf {m : ℕ | HasWidth n m}

/-- Count admissible indices `2 ≤ n ≤ N` having minimum width `m`. -/
noncomputable def F (m N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter (fun n => 2 ≤ n ∧ f n = m)).card

/-- The source's explicit unanswered width-one question. -/
def WidthOneInfinitude : Prop := Set.Infinite {n : ℕ | 2 ≤ n ∧ f n = 1}

/-- One precise possible answer to the source's broad behavior question.
The source does not specify this as its unique target. -/
def EscapesToInfinity : Prop := Tendsto f atTop atTop

/-- Every selected factor divides the factorial. -/
@[category API, AMS 11]
theorem factor_dvd {n : ℕ} {s : Finset ℕ} (hp : s.prod id = n.factorial)
    {x : ℕ} (hx : x ∈ s) : x ∣ n.factorial := by
  rw [← hp]
  exact Finset.dvd_prod_of_mem id hx

/-- The factorial product rules out a zero factor. -/
@[category API, AMS 11]
theorem factor_pos {n : ℕ} {s : Finset ℕ} (hp : s.prod id = n.factorial)
    {x : ℕ} (hx : x ∈ s) : 0 < x := by
  have hd := factor_dvd hp hx
  have hn := Nat.factorial_ne_zero n
  by_contra h
  have hx0 : x = 0 := by omega
  subst x
  exact hn (by simpa using hd)

/-- A factorization exists on the intended domain. -/
@[category API, AMS 11]
theorem hasWidth_exists (n : ℕ) (hn : 2 ≤ n) : ∃ m, HasWidth n m := by
  have hp : (Finset.Ico 1 (n + 1)).prod id = n.factorial :=
    Finset.prod_Ico_id_eq_factorial n
  refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_, hp⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    exact Finset.mem_Icc.2 ⟨h1, by omega⟩
  · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-- The minimum width is positive on the intended domain. -/
@[category API, AMS 11]
theorem one_le_f (n : ℕ) (hn : 2 ≤ n) : 1 ≤ f n := by
  obtain ⟨m, hm⟩ := hasWidth_exists n hn
  exact le_csInf ⟨m, hm⟩ (fun _ hk => hk.1)

/-- An admissible diameter bounds the minimum. -/
@[category API, AMS 11]
theorem f_le_of_hasWidth {n m : ℕ} (hm : HasWidth n m) : f n ≤ m :=
  Nat.sInf_le hm

/-- The infimum is attained, so it is a genuine admissible minimum. -/
@[category API, AMS 11]
theorem f_hasWidth (n : ℕ) (hn : 2 ≤ n) : HasWidth n (f n) := by
  exact Nat.sInf_mem (hasWidth_exists n hn)

/-- The factorization `2! = 1 * 2` has diameter one. -/
@[category test, AMS 11]
theorem f_two : f 2 = 1 :=
  le_antisymm (Nat.sInf_le ⟨by omega, 1, {1, 2}, by decide,
    by decide, by decide, by decide⟩) (one_le_f 2 (by omega))

/-- The factorization `3! = 2 * 3` has diameter one. -/
@[category test, AMS 11]
theorem f_three : f 3 = 1 :=
  le_antisymm (Nat.sInf_le ⟨by omega, 2, {2, 3}, by decide,
    by decide, by decide, by decide⟩) (one_le_f 3 (by omega))

/-- Gaps are allowed: the factors $70,72$ give $f(7) \leq 2$. -/
@[category test, AMS 11]
theorem f_seven_le_two : f 7 ≤ 2 :=
  Nat.sInf_le ⟨by omega, 70, {70, 72}, by decide,
    by decide, by decide, by decide⟩

/-- The standard factorization `2 * 3 * ... * n` gives the trivial upper bound. -/
@[category API, AMS 11]
theorem f_le_sub_two (n : ℕ) (hn : 3 ≤ n) : f n ≤ n - 2 := by
  have hp : (Finset.Ico 2 (n + 1)).prod id = n.factorial := by
    have h := Finset.prod_eq_prod_Ico_succ_bot (show 1 < n + 1 by omega) (fun i => i)
    rw [Finset.prod_Ico_id_eq_factorial, one_mul] at h
    exact h.symm
  refine Nat.sInf_le ⟨by omega, 2, Finset.Ico 2 (n + 1), ?_, ?_, ?_, hp⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    exact Finset.mem_Icc.2 ⟨h1, by omega⟩
  · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-- A factorial equal to one cannot use two distinct endpoints. -/
@[category API, AMS 11]
theorem not_hasWidth_of_factorial_eq_one {n : ℕ} (hn : n.factorial = 1) (m : ℕ) :
    ¬ HasWidth n m := by
  rintro ⟨hm, a, s, _, ha, hb, hp⟩
  have hd1 := factor_dvd hp ha
  have hd2 := factor_dvd hp hb
  rw [hn] at hd1 hd2
  have h1 := Nat.eq_one_of_dvd_one hd1
  have h2 := Nat.eq_one_of_dvd_one hd2
  omega

/-- The specified total extension has value zero at `0`. -/
@[category test, AMS 11]
theorem f_zero : f 0 = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_of_forall_notMem ?_))
  intro m hm
  exact not_hasWidth_of_factorial_eq_one (n := 0) (by norm_num) m hm

/-- The specified total extension has value zero at `1`. -/
@[category test, AMS 11]
theorem f_one : f 1 = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_of_forall_notMem ?_))
  intro m hm
  exact not_hasWidth_of_factorial_eq_one (n := 1) (by norm_num) m hm

/-- Width one is equivalent to a product of two consecutive positive integers. -/
@[category API, AMS 11]
theorem hasWidth_one_iff {n : ℕ} :
    HasWidth n 1 ↔ ∃ a : ℕ, 0 < a ∧ n.factorial = a * (a + 1) := by
  constructor
  · rintro ⟨_, a, s, hs, ha, hb, hp⟩
    have heq : s = {a, a + 1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (hs hx)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · simpa [hx] using ha
        · simpa [hx] using hb
    have hprod : n.factorial = a * (a + 1) := by
      rw [heq, Finset.prod_pair (by omega)] at hp
      exact hp.symm
    refine ⟨a, ?_, hprod⟩
    by_contra h
    have ha0 : a = 0 := by omega
    have hz := Nat.factorial_ne_zero n
    simp [ha0] at hprod
    exact hz hprod
  · rintro ⟨a, _, hp⟩
    refine ⟨by omega, a, {a, a + 1}, ?_, by simp, by simp, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    · rw [Finset.prod_pair (by omega)]
      exact hp.symm


/-- On the intended domain, $f(n)=1$ exactly when $n!$ is a consecutive-factor product. -/
@[category API, AMS 11]
theorem f_eq_one_iff {n : ℕ} (hn : 2 ≤ n) :
    f n = 1 ↔ ∃ a : ℕ, 0 < a ∧ n.factorial = a * (a + 1) := by
  rw [← hasWidth_one_iff]
  constructor
  · intro h
    simpa [h] using f_hasWidth n hn
  · intro h
    have hlo := one_le_f n hn
    have hhi := f_le_of_hasWidth h
    omega

/-- The width-one infinitude question is equivalent to infinitely many consecutive-factor factorials. -/
@[category API, AMS 11]
theorem widthOneInfinitude_arithmetic_iff : WidthOneInfinitude ↔
    Set.Infinite {n : ℕ | 2 ≤ n ∧ ∃ a : ℕ, 0 < a ∧ n.factorial = a * (a + 1)} := by
  unfold WidthOneInfinitude
  have hsets : {n : ℕ | 2 ≤ n ∧ f n = 1} =
      {n : ℕ | 2 ≤ n ∧ ∃ a : ℕ, 0 < a ∧ n.factorial = a * (a + 1)} := by
    ext n
    constructor
    · rintro ⟨hn, hf⟩
      exact ⟨hn, (f_eq_one_iff hn).mp hf⟩
    · rintro ⟨hn, hp⟩
      exact ⟨hn, (f_eq_one_iff hn).mpr hp⟩
  rw [hsets]

/-- Two successive consecutive-factor products give an elementary exclusion certificate. -/
@[category API, AMS 11]
theorem not_consecutive_of_between {N k : ℕ}
    (hlo : k * (k + 1) < N) (hhi : N < (k + 1) * (k + 2)) :
    ¬ ∃ a : ℕ, 0 < a ∧ N = a * (a + 1) := by
  rintro ⟨a, _, hp⟩
  by_cases ha : a ≤ k
  · have hm := Nat.mul_le_mul ha (Nat.add_le_add_right ha 1)
    omega
  · have ha' : k + 1 ≤ a := by omega
    have hm : (k + 1) * (k + 2) ≤ a * (a + 1) := by
      simpa [Nat.add_assoc] using Nat.mul_le_mul ha' (Nat.add_le_add_right ha' 1)
    omega

/-- The factors $4,6$ give $f(4)=2$; no consecutive-factor representation exists. -/
@[category test, AMS 11]
theorem f_four : f 4 = 2 := by
  have hw : HasWidth 4 2 := by
    refine ⟨by decide, 4, {4, 6}, by decide, by decide, by decide, ?_⟩
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  have hlo := one_le_f 4 (by decide)
  have hhi := f_le_of_hasWidth hw
  have hne : f 4 ≠ 1 := by
    intro h
    exact not_consecutive_of_between (k := 4) (by norm_num) (by norm_num)
      ((f_eq_one_iff (by decide)).mp h)
  omega

/-- The factors $4,5,6$ give $f(5)=2$; no consecutive-factor representation exists. -/
@[category test, AMS 11]
theorem f_five : f 5 = 2 := by
  have hw : HasWidth 5 2 := by
    refine ⟨by decide, 4, {4, 5, 6}, by decide, by decide, by decide, ?_⟩
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  have hlo := one_le_f 5 (by decide)
  have hhi := f_le_of_hasWidth hw
  have hne : f 5 ≠ 1 := by
    intro h
    exact not_consecutive_of_between (k := 10) (by norm_num) (by norm_num)
      ((f_eq_one_iff (by decide)).mp h)
  omega

/-- The factors $8,9,10$ give $f(6)=2$; no consecutive-factor representation exists. -/
@[category test, AMS 11]
theorem f_six : f 6 = 2 := by
  have hw : HasWidth 6 2 := by
    refine ⟨by decide, 8, {8, 9, 10}, by decide, by decide, by decide, ?_⟩
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  have hlo := one_le_f 6 (by decide)
  have hhi := f_le_of_hasWidth hw
  have hne : f 6 ≠ 1 := by
    intro h
    exact not_consecutive_of_between (k := 26) (by norm_num) (by norm_num)
      ((f_eq_one_iff (by decide)).mp h)
  omega

/-- The factors $70,72$ give $f(7)=2$; no consecutive-factor representation exists. -/
@[category test, AMS 11]
theorem f_seven : f 7 = 2 := by
  have hw : HasWidth 7 2 := by
    refine ⟨by decide, 70, {70, 72}, by decide, by decide, by decide, ?_⟩
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  have hlo := one_le_f 7 (by decide)
  have hhi := f_le_of_hasWidth hw
  have hne : f 7 ≠ 1 := by
    intro h
    exact not_consecutive_of_between (k := 70) (by norm_num) (by norm_num)
      ((f_eq_one_iff (by decide)).mp h)
  omega

/-- Escape to infinity would force every fixed-width fibre to be finite. -/
@[category API, AMS 11]
theorem escapes_implies_finite_fibre (h : EscapesToInfinity) (m : ℕ) :
    Set.Finite {n : ℕ | f n = m} := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp h) (m + 1)
  apply (Set.finite_lt_nat N).subset
  intro n hn
  change n < N
  by_contra hge
  have hb := hN n (by omega)
  change f n = m at hn
  omega

/-- An affirmative escape-to-infinity result would give a negative answer
to the width-one infinitude question. -/
@[category API, AMS 11]
theorem escapes_implies_not_widthOneInfinitude (h : EscapesToInfinity) :
    ¬ WidthOneInfinitude := by
  intro hi
  exact hi ((escapes_implies_finite_fibre h 1).subset (fun _ hn => hn.2))

/-- Brocard--Ramanujan solutions give diameter-two factorizations.
Thus proving escape to infinity also controls this neighboring open problem. -/
@[category API, AMS 11]
theorem brocard_implies_width_two {n b : ℕ} (hb : 2 ≤ b)
    (heq : n.factorial + 1 = b ^ 2) : HasWidth n 2 := by
  have hbase : b - 1 + 2 = b + 1 := by omega
  have hprod : (b - 1) * (b + 1) = n.factorial := by
    have hsub : b - 1 + 1 = b := by omega
    nlinarith
  refine ⟨by omega, b - 1, {b - 1, b + 1}, ?_, by simp, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hbase] <;> omega
  · simp [hbase]
  · rw [Finset.prod_pair (by omega)]
    exact hprod

/-- Every Brocard--Ramanujan solution gives the upper bound two. -/
@[category API, AMS 11]
theorem brocard_implies_f_le_two {n b : ℕ} (hb : 2 ≤ b)
    (heq : n.factorial + 1 = b ^ 2) : f n ≤ 2 :=
  f_le_of_hasWidth (brocard_implies_width_two hb heq)

/--
Let $f(n)$ denote the minimal $m\geq 1$ such that
$$n! = a_1\cdots a_t$$
with $a_1<\cdots<a_t=a_1+m$. What is the behaviour of $f(n)$?

One precise question about this behaviour is whether $f(n)\to\infty$.
This does not specify the full asymptotic behaviour requested by the source.
-/
@[category research open, AMS 11]
theorem erdos_393 : answer(sorry) ↔ Tendsto f atTop atTop := by
  sorry

/-- Erdős and Graham [ErGr80, p. 76] ask whether $f(n)=1$ for infinitely many $n$.
This is the consecutive-factor factorial question characterized by `f_eq_one_iff`. -/
@[category research open, AMS 11]
theorem erdos_393.variants.infinitely_often_one : answer(sorry) ↔
    Set.Infinite {n : ℕ | 2 ≤ n ∧ f n = 1} := by
  sorry

/-- Berend--Osgood [BeOs92] implies that, for every fixed positive width $m$,
$F_m(N)/N\to0$. Here $F_m(N)$ counts $2\leq n\leq N$ with $f(n)=m$.
For fixed $m$, each such factorial is the value of one of finitely many polynomials
$\prod_{j\in S}(x+j)$ with $\{0,m\}\subseteq S\subseteq\{0,\ldots,m\}$.
-/
@[category research solved, AMS 11]
theorem erdos_393.variants.berend_osgood :
    ∀ m : ℕ, 1 ≤ m →
      Tendsto (fun N : ℕ => (F m N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  sorry

/-- Bui--Pratt--Zaharescu [BPZ23, Theorem 1.1] implies
$F_m(N)\ll_m N^{33/34}$. The constant may depend on $m$, but is uniform in $N$.
Summing their dyadic estimate over the finite polynomial family for width $m$
gives this counting bound. -/
@[category research solved, AMS 11]
theorem erdos_393.variants.bui_pratt_zaharescu :
    ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (F m N : ℝ) ≤ C * (N : ℝ) ^ (33 / 34 : ℝ) := by
  sorry

/-- Luca [Lu02] proves that the $abc$ conjecture implies finiteness of solutions
to $P(x)=n!$ for every integer polynomial of degree at least two.
The finite polynomial families for bounded widths then imply $f(n)\to\infty$.
The hypothesis is the statement of `ABC.abc`; its conjecture placeholder is not used as a proof.
-/
@[category research solved, AMS 11]
theorem erdos_393.variants.luca (habc : type_of% ABC.abc) : Tendsto f atTop atTop := by
  sorry

end Erdos393
