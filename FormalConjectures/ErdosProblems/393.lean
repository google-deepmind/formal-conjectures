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
-/

@[expose] public section

open Filter Asymptotics
open scoped Nat

namespace Erdos393

/--
`f n` is $f(n)$, the minimal $m \geq 1$ such that $n! = a_1 \cdots a_t$ with
$a_1 < \cdots < a_t = a_1 + m$. The factors are recorded as a finite set
$s \subseteq [a, a + m]$ of natural numbers that contains $a = a_1$ and $a + m = a_t$. Since
$m \geq 1$ there are at least two factors, and they are positive because $n! \neq 0$.

Such a factorisation exists for $n \geq 2$. For $n \leq 1$ there is none, since $n! = 1$, and
`f n` is the junk value `0`.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
    ∏ i ∈ s, i = n !}

/-- For $n \geq 2$ the factorisation $n! = 1 \cdot 2 \cdots n$ exists, so `f n` is a true
minimum and $f(n) \geq 1$. -/
@[category test, AMS 11]
theorem one_le_f (n : ℕ) (hn : 2 ≤ n) : 1 ≤ f n := by
  have hprod : ∏ i ∈ Finset.Ico 1 (n + 1), i = n ! := Finset.prod_Ico_id_eq_factorial n
  refine le_csInf ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_, hprod⟩ fun _ hm ↦ hm.1
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    exact Finset.mem_Icc.2 ⟨h1, by omega⟩
  · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-- $3! = 2 \cdot 3$, so $f(3) = 1$. -/
@[category test, AMS 11]
theorem f_three : f 3 = 1 :=
  le_antisymm (Nat.sInf_le ⟨le_rfl, 2, {2, 3}, by decide, by decide, by decide, by decide⟩)
    (one_le_f 3 (by norm_num))

/-- The factors need not be consecutive integers: $7! = 70 \cdot 72$, so $f(7) \leq 2$. -/
@[category test, AMS 11]
theorem f_seven_le_two : f 7 ≤ 2 :=
  Nat.sInf_le ⟨by norm_num, 70, {70, 72}, by decide, by decide, by decide, by decide⟩

/-- The factorisation $n! = 2 \cdot 3 \cdots n$ shows that $f(n) \leq n - 2$ for $n \geq 3$. -/
@[category test, AMS 11]
theorem f_le_sub_two (n : ℕ) (hn : 3 ≤ n) : f n ≤ n - 2 := by
  have hprod : ∏ i ∈ Finset.Ico 2 (n + 1), i = n ! := by
    have h := Finset.prod_eq_prod_Ico_succ_bot (show 1 < n + 1 by omega) (fun i ↦ i)
    rw [Finset.prod_Ico_id_eq_factorial, one_mul] at h
    exact h.symm
  refine Nat.sInf_le ⟨by omega, 2, Finset.Ico 2 (n + 1), ?_, ?_, ?_, hprod⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    exact Finset.mem_Icc.2 ⟨h1, by omega⟩
  · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

/-- $1! = 1$ is not a product of two or more distinct positive integers, so `f 1` is the junk
value `0`. -/
@[category test, AMS 11]
theorem f_one : f 1 = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_of_forall_notMem ?_))
  rintro m ⟨hm, a, s, -, ha, hb, hs⟩
  have h1 : a ∣ ∏ i ∈ s, i := Finset.dvd_prod_of_mem (fun i ↦ i) ha
  have h2 : a + m ∣ ∏ i ∈ s, i := Finset.dvd_prod_of_mem (fun i ↦ i) hb
  rw [hs, Nat.factorial_one] at h1 h2
  have ha1 := Nat.eq_one_of_dvd_one h1
  have hb1 := Nat.eq_one_of_dvd_one h2
  omega

/--
Let $f(n)$ denote the minimal $m\geq 1$ such that
$$n! = a_1\cdots a_t$$
with $a_1<\cdots <a_t=a_1+m$. What is the behaviour of $f(n)$?

We formalise the question as: does $f(n) \to \infty$? A result of Luca [Lu02] implies a positive
answer, conditional on the $abc$ conjecture (see `Erdos393.erdos_393.variants.luca`).
-/
@[category research open, AMS 11]
theorem erdos_393 : answer(sorry) ↔ Tendsto f atTop atTop := by
  sorry

/--
Erdős and Graham [ErGr80, p. 76] write that they do not even know whether $f(n) = 1$ for infinitely
many $n$, that is, whether a factorial is the product of two consecutive integers infinitely
often.
-/
@[category research open, AMS 11]
theorem erdos_393.variants.infinitely_often_one :
    answer(sorry) ↔ {n : ℕ | f n = 1}.Infinite := by
  sorry

/--
Let $F_m(N)$ count the number of $n \leq N$ such that $f(n) = m$. A theorem of Berend and
Osgood [BeOs92] implies that, for each fixed $m$, $F_m(N) = o(N)$, that is,
$\{n : f(n) = m\}$ has natural density $0$.

They proved that, for every $P \in \mathbb{Z}[x]$ of degree at least $2$, the set of $n$ such
that $P(x) = n!$ has an integer solution has density $0$. For $m \geq 1$ this applies because
$f(n) = m$ gives $n! = P(a_1)$ for one of the finitely many polynomials
$P(x) = \prod_{j \in S} (x + j)$ with $\{0, m\} \subseteq S \subseteq \{0, \ldots, m\}$. For
$m = 0$ the set is $\{0, 1\}$ (the junk values), so the statement is trivial.
-/
@[category research solved, AMS 11]
theorem erdos_393.variants.berend_osgood (m : ℕ) :
    {n : ℕ | f n = m}.HasDensity 0 := by
  sorry

/--
A theorem of Bui, Pratt, and Zaharescu [BPZ23] implies that, for each fixed $m$,
$$F_m(N) \ll_m N^{33/34},$$
where $F_m(N)$ is the number of $n \leq N$ such that $f(n) = m$.

They proved that, for every $P \in \mathbb{Z}[x]$ of degree at least $2$, the number of
$N \leq n < 2N$ such that $P(x) = n!$ has an integer solution is $\ll_P N^{33/34}$. Summing over
the finitely many polynomials in `Erdos393.erdos_393.variants.berend_osgood` and over the dyadic
ranges $[2^i, 2^{i+1})$ gives the bound for $n \leq N$.
-/
@[category research solved, AMS 11]
theorem erdos_393.variants.bui_pratt_zaharescu (m : ℕ) :
    (fun N : ℕ ↦ (({n : ℕ | f n = m} ∩ Set.Iic N).ncard : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ (33 / 34 : ℝ)) := by
  sorry

/--
Luca [Lu02] proved that the $abc$ conjecture implies that, for every $P \in \mathbb{Z}[x]$ of
degree at least $2$, the equation $P(x) = n!$ has only finitely many solutions. As remarked on
erdosproblems.com, this implies that $f(n) \to \infty$, conditional on the $abc$ conjecture
(`ABC.abc`).
-/
@[category research solved, AMS 11]
theorem erdos_393.variants.luca (habc : type_of% ABC.abc) : Tendsto f atTop atTop := by
  sorry

end Erdos393
