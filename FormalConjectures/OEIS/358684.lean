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
import FormalConjectures.Util.ProblemImports

/-!
$a(n)$ is the minimum integer $k$ such that the smallest prime factor of the
$n$-th Fermat number exceeds $2^(2^n - k)$.

*References:*
- [A034693](https://oeis.org/A034693)
- [SA22](https://doi.org/10.26493/2590-9770.1473.ec5) Lorenzo Sauras-Altuzarra, *Some properties of the factors of Fermat numbers*, Art Discrete Appl. Math. (2022).
-/


open Nat

/--
A358684: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat
number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe
 since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.
-/
def a (n : ℕ) : ℕ :=
  let pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)

/--
The "original" definition: $a'(n)$ is the minimum $k$ such that $P_n > 2^{2^n - k}$.
We use `Nat.find` which returns the smallest natural number satisfying a predicate.
-/
noncomputable def a' (n : ℕ) : ℕ :=
  let Pn := minFac (fermatNumber n)
  Nat.find (show ∃ k, Pn > 2 ^ (2 ^ n - k) from by
    use 2^n
    simp only [tsub_self, pow_zero]
    simp [Pn]
    unfold Nat.fermatNumber
    exact (Nat.minFac_prime (by norm_num)).one_lt
  )

/--
The minimization definition is equivalent to the closed form.
-/
@[category API, AMS 11]
theorem a_equiv_a' (n : ℕ) : a n = a' n := by
  sorry

@[category test, AMS 11]
theorem zero : a 0 = 0 := by
  simp [a]
  norm_num [Nat.log2]

@[category test, AMS 11]
theorem one : a 1 = 0 := by
  simp [a]
  norm_num [Nat.log2]

@[category test, AMS 11]
theorem two : a 2 = 0 := by
  norm_num [a]
  norm_num [Nat.log2]

@[category test, AMS 11]
theorem three : a 3 = 0 := by
  rw[a]
  norm_num only [Nat.log2_eq_log_two,Nat.fermatNumber]

@[category test, AMS 11]
theorem four : a 0 = 0 := by
  norm_num[a]
  norm_num[Nat.log2]

@[category test, AMS 11]
theorem five : a 5 = 23 := by
  norm_num[a]
  norm_num [fermatNumber,Nat.log2_eq_log_two]

@[category test, AMS 11]
theorem six : a 6 = 46 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 11]
theorem seven : a 7 = 73 := by
  sorry

/--
Conjecture: the dyadic valuation of A093179(n) - 1 does not exceed 2^n - a(n).

A093179(n) is minFac(fermatNumber n), the smallest prime factor of the n-th Fermat number.
The conjecture states that if $P_n$ is the smallest prime factor of the $n$-th Fermat number,
then $\nu_2(P_n - 1) \le 2^n - a(n)$.
Substituting the definition of $a(n)$, this is equivalent to $\nu_2(P_n - 1) \le \lfloor \log_2(P_n) \rfloor$.

This is Conjecture 3.4 in [SA22].
-/
@[category research open, AMS 11]
theorem oeis_358684_conjecture_0 (n : ℕ) :
  padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n := by
  delta fermatNumber and a
  rw [Nat.sub_sub_self]
  · rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le (by decide)
    refine le_trans ?_ <| sub_le _ 1
    apply Nat.ordProj_le 2
    exact Nat.sub_ne_zero_of_lt (Nat.minFac_prime (by norm_num)).one_lt
  · rw [Nat.log2_eq_log_two]
    have : (2 ^ 2 ^ n) + 1 < 2 ^ ((2 ^ n) + 1) := by
      simp [pow_add, mul_two]
    refine Nat.le_of_lt_succ <| (2).log_lt_of_lt_pow ?_ ?_
    · exact Nat.minFac_pos _|>.ne'
    · exact (Nat.minFac_le (by bound)).trans_lt this

