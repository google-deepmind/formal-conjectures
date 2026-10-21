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
public import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 731

*References:*
- [erdosproblems.com/731](https://www.erdosproblems.com/731)
- [EGRS75] Erdős, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G.,
  *On the prime factors of $\binom{2n}{n}$*. Math. Comp. 29 (1975), 83-92.
  [PDF](https://www.renyi.hu/~p_erdos/1975-27.pdf)
-/

@[expose] public section

namespace Erdos731

/-- The least integer $m \geq 1$ such that $m \nmid \binom{2n}{n}$, denoted $A(n)$ in [EGRS75].
The set is nonempty, since it contains $\binom{2n}{n}+1$ (see `leastNonDivisor_spec`), so `sInf`
is the true minimum. The condition `0 < m` excludes `m = 0`. -/
noncomputable def leastNonDivisor (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ¬ m ∣ n.centralBinom}

/-- `leastNonDivisor n` is a positive integer that does not divide $\binom{2n}{n}$. -/
@[category API, AMS 11]
theorem leastNonDivisor_spec (n : ℕ) :
    0 < leastNonDivisor n ∧ ¬ leastNonDivisor n ∣ n.centralBinom := by
  have h : {m : ℕ | 0 < m ∧ ¬ m ∣ n.centralBinom}.Nonempty :=
    ⟨n.centralBinom + 1, by omega, Nat.not_dvd_of_pos_of_lt n.centralBinom_pos (by omega)⟩
  exact Nat.sInf_mem h

/-- $A(1)=3$, since $\binom{2}{1}=2$ is divisible by $1$ and $2$ but not by $3$. -/
@[category test, AMS 11]
theorem leastNonDivisor_one : leastNonDivisor 1 = 3 := by
  have hc : (1 : ℕ).centralBinom = 2 := by decide +kernel
  have h3 : 3 ∈ {m : ℕ | 0 < m ∧ ¬ m ∣ (1 : ℕ).centralBinom} :=
    ⟨by norm_num, by rw [hc]; decide⟩
  unfold leastNonDivisor
  refine le_antisymm (Nat.sInf_le h3) (le_csInf ⟨3, h3⟩ fun m hm => ?_)
  obtain ⟨hm0, hm⟩ := hm
  rw [hc] at hm
  by_contra! hlt
  interval_cases m <;> simp at hm

def erdos_731.answer : ℕ → ℝ := sorry

/--
Find some reasonable function $f(n)$ such that, for almost all integers $n$, the least integer
$m$ such that $m\nmid \binom{2n}{n}$ satisfies
$$m\sim f(n).$$

Here "almost all" means natural density $1$, and $m \sim f(n)$ means that for every
$\varepsilon>0$ the set of $n$ with $|m/f(n)-1|<\varepsilon$ has density $1$.
-/
@[category research open, question value, AMS 11]
theorem erdos_731 : ∀ ε > (0 : ℝ),
    {n : ℕ | |(leastNonDivisor n : ℝ) / erdos_731.answer n - 1| < ε}.HasDensity 1 := by
  sorry

/--
A problem of Erdős, Graham, Ruzsa, and Straus [EGRS75], who say it is 'not hard to show that',
for almost all $n$, the minimal such $m$ satisfies
$$m=\exp((\log n)^{1/2+o(1)}).$$

[EGRS75, (8), p. 91] states this as: for every $\varepsilon>0$, for all $n$ outside a set of
density $0$, $\exp((\log n)^{1/2-\varepsilon}) < m < \exp((\log n)^{1/2+\varepsilon})$.
-/
@[category research solved, AMS 11]
theorem erdos_731.variants.egrs75 : ∀ ε > (0 : ℝ),
    {n : ℕ | Real.exp (Real.log n ^ ((1 : ℝ) / 2 - ε)) < (leastNonDivisor n : ℝ) ∧
      (leastNonDivisor n : ℝ) < Real.exp (Real.log n ^ ((1 : ℝ) / 2 + ε))}.HasDensity 1 := by
  sorry

end Erdos731
