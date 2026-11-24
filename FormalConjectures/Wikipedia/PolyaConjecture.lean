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
# Pólya's Conjecture and the Summatory Liouville Function

Let $\lambda(n) = (-1)^{\Omega(n)}$ denote the Liouville function (`ArithmeticFunction.liouville`,
`OEIS A008836`) and $L(n) = \sum_{k=1}^n \lambda(k)$ denote the summatory Liouville function
(`OEIS A002819`). In 1919, George Pólya [Po19] studied the assertion $L(n) \le 0$ for every
integer $n \ge 2$, showing that this bound entails the Riemann Hypothesis. Haselgrove [Ha58]
disproved this inequality in 1958, and Tanaka [Ta80] determined the smallest counterexample
$n = 906{,}150{,}257$. Humphries [Hu13] proved conditionally (assuming the Riemann Hypothesis and
additional hypotheses on zeta zeros) that the set of $n$ with $L(n) > 0$ possesses a positive
logarithmic density $\delta \in (0, 1/2]$; establishing this unconditionally remains open.

*References:*
- [Wikipedia: Pólya conjecture](https://en.wikipedia.org/wiki/P%C3%B3lya_conjecture)
- [OEIS A008836](https://oeis.org/A008836)
- [OEIS A002819](https://oeis.org/A002819)
- [Po19] G. Pólya, *Verschiedene Bemerkungen zur Zahlentheorie*, Jahresber. Deutsch. Math.-Verein.
  **28** (1919), 31–40.
- [Ha58] C. B. Haselgrove, *A disproof of a conjecture of Pólya*, Mathematika **5** (1958), no. 2,
  141–145. https://doi.org/10.1112/S0025579300001480
- [Ta80] M. Tanaka, *A numerical investigation on cumulative sum of the Liouville function*, Tokyo
  J. Math. **3** (1980), no. 1, 187–189. https://doi.org/10.3836/tjm/1270216093
- [Hu13] P. Humphries, *The distribution of weighted sums of the Liouville function and Pólya's
  conjecture*, J. Number Theory **133** (2013), no. 2, 545–582.
  https://doi.org/10.1016/j.jnt.2012.08.011
-/

@[expose] public section

namespace PolyaConjecture

open Filter

/-- The summatory Liouville function $L(n) = \sum_{k=1}^n \lambda(k)$ (`OEIS A002819`). -/
def summatoryLiouville (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.liouville k

/-- At $n = 0$, the empty sum gives $L(0) = 0$. -/
@[category test, AMS 11]
theorem summatoryLiouville_zero : summatoryLiouville 0 = 0 := by
  decide

/-- At $n = 1$, $L(1) = \lambda(1) = 1 > 0$, explaining why Pólya's inequality restricts to
$n \ge 2$. -/
@[category test, AMS 11]
theorem summatoryLiouville_one : summatoryLiouville 1 = 1 := by
  simp [summatoryLiouville, ArithmeticFunction.liouville_apply_one]

/-- At $n = 2$, $L(2) = \lambda(1) + \lambda(2) = 0$. -/
@[category test, AMS 11]
theorem summatoryLiouville_two : summatoryLiouville 2 = 0 := by
  rw [summatoryLiouville, show Finset.Icc 1 2 = {1, 2} by decide]
  have h2 : ArithmeticFunction.cardFactors 2 = 1 :=
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
  simp [ArithmeticFunction.liouville_apply, h2]

/-- At $n = 3$, $L(3) = -1$. -/
@[category test, AMS 11]
theorem summatoryLiouville_three : summatoryLiouville 3 = -1 := by
  rw [summatoryLiouville, show Finset.Icc 1 3 = {1, 2, 3} by decide]
  have h2 : ArithmeticFunction.cardFactors 2 = 1 :=
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.cardFactors 3 = 1 :=
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_three
  simp [ArithmeticFunction.liouville_apply, h2, h3]

/-- Step recurrence $L(n + 1) = L(n) + \lambda(n + 1)$. -/
@[category API, AMS 11]
theorem summatoryLiouville_succ (n : ℕ) :
    summatoryLiouville (n + 1) = summatoryLiouville n + ArithmeticFunction.liouville (n + 1) := by
  unfold summatoryLiouville
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- Because $L(2) = 0$ and each step changes $L$ by at most $1$, the least $m \ge 2$ with
$L(m) > 0$ necessarily satisfies $L(m) = 1$. -/
@[category API, AMS 11]
theorem summatoryLiouville_eq_one_of_isLeast_pos {m : ℕ}
    (hm : IsLeast {n : ℕ | 2 ≤ n ∧ 0 < summatoryLiouville n} m) :
    summatoryLiouville m = 1 := by
  rcases hm with ⟨⟨hm2, hpos⟩, hmin⟩
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have hmeq : m = 2 := by omega
    subst hmeq
    rw [summatoryLiouville_two] at hpos
    omega
  have hprev_le : summatoryLiouville (m - 1) ≤ 0 := by
    by_contra hgt
    push Not at hgt
    have hle := hmin ⟨by omega, hgt⟩
    omega
  have hstep : summatoryLiouville m =
      summatoryLiouville (m - 1) + ArithmeticFunction.liouville m := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using summatoryLiouville_succ (m - 1)
  have hliouv_le : ArithmeticFunction.liouville m ≤ 1 := by
    rw [ArithmeticFunction.liouville_apply (by omega)]
    rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors m) with h1 | h1 <;> omega
  omega

/--
**Pólya's Conjecture** [Po19], disproved by Haselgrove [Ha58]: It is false that $L(n) \le 0$ for
every integer $n \ge 2$.
-/
@[category research solved, AMS 11]
theorem polya_conjecture : ¬ ∀ n : ℕ, 2 ≤ n → summatoryLiouville n ≤ 0 := by
  sorry

/--
**Infinitely Many Positive Values of $L(n)$** [Ha58]: There exist infinitely many natural numbers
$n$ with $L(n) > 0$.
-/
@[category research solved, AMS 11]
theorem polya_conjecture.variants.infinitely_many_pos :
    ∃ᶠ n : ℕ in atTop, 0 < summatoryLiouville n := by
  sorry

/--
**Tanaka's Smallest Counterexample** [Ta80]: The smallest integer $n \ge 2$ with $L(n) > 0$ is
$n = 906{,}150{,}257$ (at which $L(n) = 1$ by `summatoryLiouville_eq_one_of_isLeast_pos`).
-/
@[category research solved, AMS 11]
theorem polya_conjecture.variants.tanaka_smallest_counterexample :
    IsLeast {n : ℕ | 2 ≤ n ∧ 0 < summatoryLiouville n} 906150257 := by
  sorry

/--
**Positive Logarithmic Density of $\{n \mid L(n) > 0\}$**: There exists $\delta \in (0, 1 / 2]$
such that $\{n \in \mathbb{N} \mid L(n) > 0\}$ has logarithmic density $\delta$
(`Set.HasLogDensity`; including $n = 1$ leaves the logarithmic density unchanged).

Humphries [Hu13, Theorem 1.5] proved this conditionally assuming the Riemann Hypothesis and
additional hypotheses on the nontrivial zeros of $\zeta(s)$; this statement is the unconditional
form with those hypotheses removed.
-/
@[category research open, AMS 11]
theorem polya_conjecture.variants.positive_log_density :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ {n : ℕ | 0 < summatoryLiouville n}.HasLogDensity δ := by
  sorry

end PolyaConjecture
