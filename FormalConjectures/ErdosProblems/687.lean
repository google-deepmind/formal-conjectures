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
public import FormalConjectures.GreensOpenProblems.«46»

/-!
# Erdős Problem 687

*References:*
- [erdosproblems.com/687](https://www.erdosproblems.com/687)
- [Ben Green's Open Problem 46](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.46):
  the same question; see `Green46` in `FormalConjectures.GreensOpenProblems.«46»`.
- [OEIS A058989](https://oeis.org/A058989): the values $Y(p_n)$, where $p_n$ is the $n$-th prime.
- [OEIS A048670](https://oeis.org/A048670): Jacobsthal's function of $\prod_{p \leq p_n} p$,
  which is $Y(p_n) + 1$.
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math. Acad. Sci.
  Hungar. 33 (1979), 71-80.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  6 (1980), 89-115.
- [Er96b] Erdős, Paul, *Some problems I presented or planned to present in my short talk*.
  Analytic number theory, Vol. 1 (Allerton Park, IL, 1995), Progr. Math. 138 (1996), 333-335.
- [Iw78] Iwaniec, Henryk, *On the problem of Jacobsthal*. Demonstratio Math. 11 (1978), 225-232.
  [doi:10.1515/dema-1978-0121](https://doi.org/10.1515/dema-1978-0121)
- [MaPo90] Maier, Helmut and Pomerance, Carl, *Unusually large gaps between consecutive primes*.
  Trans. Amer. Math. Soc. 322 (1990), 201-237.
- [FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence,
  *Long gaps between primes*. J. Amer. Math. Soc. 31 (2018), 65-105.
  [arXiv:1412.5029](https://arxiv.org/abs/1412.5029)
-/

@[expose] public section

open Filter

namespace Erdos687

/--
`Y x` is $Y(x)$, the maximal $y$ such that there is a choice of congruence classes $a_p$, one
for each prime $p \leq x$, such that every integer in $[1, y]$ is congruent to at least one of
the $a_p \pmod{p}$. The covering condition is `Green46.IsCoveredByResidues x y`.

We take $x$ to be a natural number, since $Y(x)$ only depends on $\lfloor x \rfloor$. The set of
such $y$ contains $0$ and is bounded by $\prod_{p \leq x} p$
(`Erdos687.lt_primorial_of_isCoveredByResidues`), so `sSup` is its maximum. $Y(x) = 0$ for
$x < 2$.
-/
noncomputable def Y (x : ℕ) : ℕ :=
  sSup {y : ℕ | Green46.IsCoveredByResidues x y}

/-- `Green46.maxY` is `Y` cast to `ℝ`. -/
@[category test, AMS 11]
theorem maxY_eq_Y (x : ℕ) : Green46.maxY x = Y x := rfl

/-- If $[1, y]$ is covered by classes $a_p \pmod{p}$, $p \leq x$, then $y < \prod_{p \leq x} p$:
by the Chinese remainder theorem some integer in $[1, \prod_{p \leq x} p]$ lies in none of the
classes. -/
@[category test, AMS 11]
theorem lt_primorial_of_isCoveredByResidues {x y : ℕ} (h : Green46.IsCoveredByResidues x y) :
    y < primorial x := by
  sorry

/-- With the single prime $2$, one class covers $1$ but no class covers both $1$ and $2$, so
$Y(2) = 1$. -/
@[category test, AMS 11]
theorem Y_two : Y 2 = 1 := by
  have h1 : Green46.IsCoveredByResidues 2 1 := by
    refine ⟨fun _ ↦ 1, fun m hm ↦ ⟨2, le_rfl, Nat.prime_two, ?_⟩⟩
    have := Finset.mem_Icc.1 hm
    show m % 2 = 1 % 2
    omega
  have h2 : ∀ y, Green46.IsCoveredByResidues 2 y → y ≤ 1 := by
    rintro y ⟨a, ha⟩
    by_contra hy
    obtain ⟨p, hp2, hp, hp1⟩ := ha 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    obtain ⟨q, hq2, hq, hq1⟩ := ha 2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rw [le_antisymm hp2 hp.two_le] at hp1
    rw [le_antisymm hq2 hq.two_le] at hq1
    exact absurd (hp1.trans hq1.symm) (by decide)
  rw [Y]
  exact IsGreatest.csSup_eq ⟨h1, h2⟩

/-- The classes $1 \pmod 2$ and $2 \pmod 3$ cover $1, 2, 3$, but no choice of classes modulo
$2$ and $3$ covers $1, 2, 3, 4$, so $Y(3) = 3$. -/
@[category test, AMS 11]
theorem Y_three : Y 3 = 3 := by
  have h1 : Green46.IsCoveredByResidues 3 3 := by
    refine ⟨fun p ↦ if p = 2 then 1 else 2, fun m hm ↦ ?_⟩
    obtain ⟨hm1, hm3⟩ := Finset.mem_Icc.1 hm
    interval_cases m
    · exact ⟨2, by norm_num, Nat.prime_two, by decide⟩
    · exact ⟨3, le_rfl, Nat.prime_three, by decide⟩
    · exact ⟨2, by norm_num, Nat.prime_two, by decide⟩
  have h2 : ∀ y, Green46.IsCoveredByResidues 3 y → y ≤ 3 := by
    rintro y ⟨a, ha⟩
    by_contra hy
    have key : ∀ m, 1 ≤ m → m ≤ 4 → m % 2 = a 2 % 2 ∨ m % 3 = a 3 % 3 := by
      intro m hm1 hm4
      obtain ⟨p, hp3, hp, hpm⟩ := ha m (Finset.mem_Icc.2 ⟨hm1, by omega⟩)
      interval_cases p
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact Or.inl hpm
      · exact Or.inr hpm
    have k1 := key 1 le_rfl (by norm_num)
    have k2 := key 2 (by norm_num) (by norm_num)
    have k3 := key 3 (by norm_num) (by norm_num)
    have k4 := key 4 (by norm_num) le_rfl
    omega
  rw [Y]
  exact IsGreatest.csSup_eq ⟨h1, h2⟩

/--
Let $Y(x)$ be the maximal $y$ such that there exists a choice of congruence classes $a_p$ for
all primes $p\leq x$ such that every integer in $[1,y]$ is congruent to at least one of the
$a_p\pmod{p}$. Give good estimates for $Y(x)$.

We formalise this as determining $Y(x)$ up to constant factors.
-/
@[category research open, AMS 11]
theorem erdos_687.parts.i :
    (fun x : ℕ ↦ (Y x : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
In particular, can one prove that $Y(x)=o(x^2)$?
-/
@[category research open, AMS 11]
theorem erdos_687.parts.ii : answer(sorry) ↔
    (fun x : ℕ ↦ (Y x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ) ^ 2) := by
  sorry

/--
Or, even stronger, can one prove that $Y(x)\ll x^{1+o(1)}$?

We read $Y(x)\ll x^{1+o(1)}$ as $Y(x) = O(x^{1+\varepsilon})$ for every fixed
$\varepsilon > 0$.
-/
@[category research open, AMS 11]
theorem erdos_687.parts.iii : answer(sorry) ↔
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop] (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  sorry

/--
Iwaniec's upper bound for Jacobsthal's function [Iw78] gives $Y(x) \ll x^2$.
-/
@[category research solved, AMS 11]
theorem erdos_687.variants.iwaniec :
    (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop] (fun x : ℕ ↦ (x : ℝ) ^ 2) := by
  sorry

/--
Ford, Green, Konyagin, Maynard and Tao [FGKMT18] proved
$$Y(x) \gg \frac{x \log x \log\log\log x}{\log\log x}.$$
-/
@[category research solved, AMS 11]
theorem erdos_687.variants.fgkmt :
    (fun x : ℕ ↦ (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
      Real.log (Real.log x)) =O[atTop] (fun x : ℕ ↦ (Y x : ℝ)) := by
  sorry

/--
Maier and Pomerance [MaPo90] conjectured that $Y(x) \ll x(\log x)^{2+o(1)}$ (in this form it is
stated in [FGKMT18]).

We read this as $Y(x) = O(x(\log x)^{2+\varepsilon})$ for every fixed $\varepsilon > 0$.
-/
@[category research open, AMS 11]
theorem erdos_687.variants.maier_pomerance :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 + ε)) := by
  sorry

end Erdos687
