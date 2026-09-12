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
# Erdős Problem 423

*References:*
- [erdosproblems.com/423](https://www.erdosproblems.com/423)
- [Er77c] Erdős, P., *Problems and results on combinatorial number theory. III*,
  Number theory day (Proc. Conf., Rockefeller Univ., New York, 1976), 1977, pp. 43–72.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*, Monographies de L'Enseignement Mathématique (1980).
- [Cu25] Cushman, A., *A Note on the Sum-Product Problem and the Convex Sumset Problem*.
  arXiv:2512.13849 (2025).
- [Ta26] Tang, Q., *The Hofstadter consecutive-sum sequence omits infinitely many positive
  integers*. arXiv:2603.09939 (2026).
- [Bolan] Bolan, M., *Hofstader–Ulam Sequence*,
  https://github.com/mjtb49/HofstaderUlam/blob/main/HofstaderUlamSequence.pdf
- [OEIS A005243](https://oeis.org/A005243)
-/

open Finset BigOperators Filter Asymptotics

namespace Erdos423

/-- `IsConsecutiveBlockSum a k m` means that $m$ equals the sum of at least two
    consecutive terms of the sequence $a$, using indices from $\{1, \ldots, k - 1\}$.
    That is, there exist $i, j$ with $1 \le i$, $i + 1 \le j$, $j \le k - 1$ such that
    $m = a(i) + a(i+1) + \cdots + a(j)$. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$,
$a(k)$ is the least integer $> a(k-1)$ that equals the sum of at least two consecutive terms from
$\{a(1), \ldots, a(k-1)\}$. The sequence begins $1, 2, 3, 5, 6, 8, 10, 11, \ldots$. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

/-- The third term of the Hofstadter sequence is $a(3) = 3 = a(1) + a(2) = 1 + 2$. -/
@[category test, AMS 5 11]
theorem erdos_423.test.a3 : ∀ a : ℕ → ℕ, IsHofstadterSeq a → a 3 = 3 := by
  intro a ⟨ha1, ha2, hk⟩
  obtain ⟨⟨i, j, hi, hij, hjk, hsum⟩, _, _⟩ := hk 3 (by omega)
  have : i = 1 ∧ j = 2 := by omega
  obtain ⟨rfl, rfl⟩ := this
  simp only [show Finset.Icc 1 2 = {1, 2} from by decide,
    Finset.sum_pair (show (1 : ℕ) ≠ 2 from by decide), ha1, ha2] at hsum
  omega

/-- The fourth term of the Hofstadter sequence is $a(4) = 5 = a(2) + a(3) = 2 + 3$. -/
@[category test, AMS 5 11]
theorem erdos_423.test.a4 : ∀ a : ℕ → ℕ, IsHofstadterSeq a → a 4 = 5 := by
  intro a ⟨ha1, ha2, hk⟩
  have ha3 : a 3 = 3 := erdos_423.test.a3 a ⟨ha1, ha2, hk⟩
  obtain ⟨⟨i, j, hi, hij, hjk, hsum⟩, hlt, hmin⟩ := hk 4 (by omega)
  -- Since `j ≤ 3`, the possible pairs `(i, j)` are `(1, 2)`, `(2, 3)`, and `(1, 3)`.
  have h_ij : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by omega
  rcases h_ij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [show Finset.Icc 1 2 = {1, 2} from by decide,
      Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), ha1, ha2] at hsum
    rw [ha3] at hlt
    omega
  · simp only [show Finset.Icc 2 3 = {2, 3} from by decide,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), ha2, ha3] at hsum
    omega
  · rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
      Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), ha1, ha2, ha3] at hsum
    rw [ha3] at hlt
    have ha4_eq : a 4 = 6 := by omega
    have h3_lt_5 : a 3 < 5 := by omega
    have h5_lt_a4 : 5 < a 4 := by omega
    exfalso
    apply hmin 5 h3_lt_5 h5_lt_a4
    refine ⟨2, 3, by omega, by omega, by omega, ?_⟩
    rw [show Finset.Icc 2 3 = {2, 3} from by decide,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), ha2, ha3]

/--
Erdős Problem 423 [Er77c, p.71; ErGr80, p.83]:

Let $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$ let $a(k)$ be the least integer greater
than $a(k-1)$ that is a sum of at least two consecutive terms of the sequence.
What is the asymptotic behaviour of this sequence? It seems likely that $a_n = n + o(n)$.
-/
@[category research open, AMS 5 11]
theorem erdos_423 : answer(sorry) ↔
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    (fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/--
Bolan and Tang [Ta26] independently proved that $a_n-n$ is nondecreasing.
-/
@[category research solved, AMS 5 11]
theorem erdos_423.variants.nondecreasing :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m := by
  sorry

/--
Bolan and Tang [Ta26] independently proved that $a_n-n\to\infty$.
-/
@[category research solved, AMS 5 11]
theorem erdos_423.variants.unbounded :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by
  sorry

/--
Bolan and Tang [Ta26] independently proved that infinitely many positive integers do not occur in
the Hofstadter sequence.
-/
@[category research solved, AMS 5 11]
theorem erdos_423.variants.infinite_complement :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ := by
  sorry

/-- The unboundedness of $a_n-n$ is equivalent to the sequence omitting infinitely many positive
integers. -/
@[category test, AMS 5 11]
theorem erdos_423.test.unbounded_iff_infinite_complement :
    type_of% erdos_423.variants.unbounded ↔
      type_of% erdos_423.variants.infinite_complement := by
  sorry

/--
Tang [Ta26] proved $a_n \ll n^{1/(c-1)+o(1)}$ whenever every finite convex set $A$ satisfies
$|A-A|\geq |A|^{c-o(1)}$. Using the bound of Cushman [Cu25] gives
$a_n\ll n^{688/413+o(1)}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_423.variants.upper_bound :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ ε > (0 : ℝ), (fun n => (a n : ℝ)) =O[atTop]
      (fun n => (n : ℝ) ^ ((688 : ℝ) / 413 + ε)) := by
  sorry

/--
Tang [Ta26] proved the lower bound $a_n=n+\Omega(\log\log n)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_423.variants.lower_bound :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    (fun n : ℕ => Real.log (Real.log n)) =O[atTop]
      (fun n : ℕ => (a n : ℝ) - n) := by
  sorry

end Erdos423
