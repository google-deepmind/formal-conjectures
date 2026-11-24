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
# Squarefreeness of Sylvester's sequence

Sylvester's sequence (`OEIS A000058`) begins at $s_0 = 2$ with $s_{n+1} = s_n^2 - s_n + 1$, or
equivalently $s_n = 1 + \prod_{k < n} s_k$ ($2, 3, 7, 43, 1807, 3263443, \dots$). Its reciprocals
telescope via $\sum_{k < n} 1 / s_k = 1 - 1 / (s_n - 1)$ `[Sy1880]`, and distinct terms are
pairwise coprime. Makki Naciri `[MN24]` proved that no term is a perfect power
(`Nat.IsPerfectPower`), whereas whether every term $s_n$ is squarefree remains an open question
`[GKP89, Research Problem 4.65]` `[Va91]`. Related problems on Sylvester's sequence appear in
`FormalConjectures.ErdosProblems.«243»`, `FormalConjectures.ErdosProblems.«315»`, and
`FormalConjectures.OEIS.«231830»`.

*References:*
- [Wikipedia: Sylvester's sequence](https://en.wikipedia.org/wiki/Sylvester%27s_sequence)
- [OEIS A000058](https://oeis.org/A000058)
- `[Sy1880]` J. J. Sylvester, *On a point in the theory of vulgar fractions*, Amer. J. Math. **3**
  (1880), no. 4, 332–335, https://doi.org/10.2307/2369261.
- `[GKP89]` R. L. Graham, D. E. Knuth, and O. Patashnik, *Concrete Mathematics*, 2nd ed.,
  Addison-Wesley, 1989, Research Problem 4.65, p. 151.
- `[Va91]` I. Vardi, *Computational Recreations in Mathematica*, Addison-Wesley, 1991, pp. 82–89.
- `[MN24]` A. Makki Naciri, *A note on Sylvester's sequence*, Integers **24** (2024), A117, 1–7.
-/

@[expose] public section

namespace SylvesterSequence

/-- Sylvester's sequence (`OEIS A000058`), defined by $s_0 = 2$ and $s_{n+1} = s_n^2 - s_n + 1$.
Since $s_n \ge 2$, the subtraction on $\mathbb{N}$ is exact. -/
def sylvesterSeq : ℕ → ℕ
  | 0 => 2
  | n + 1 => sylvesterSeq n ^ 2 - sylvesterSeq n + 1

/-- Checks the first six terms $2, 3, 7, 43, 1807, 3263443$ of `sylvesterSeq`. -/
@[category test, AMS 11]
theorem sylvesterSeq_initial_values :
    List.map sylvesterSeq (List.range 6) = [2, 3, 7, 43, 1807, 3263443] :=
  rfl

/-- The term $s_4 = 1807 = 13 \cdot 139$ is the first composite entry of `sylvesterSeq`. -/
@[category test, AMS 11]
theorem not_prime_sylvesterSeq_four : ¬ (sylvesterSeq 4).Prime := by
  decide +kernel

/-- Although composite, $s_4 = 1807 = 13 \cdot 139$ is squarefree. -/
@[category test, AMS 11]
theorem squarefree_sylvesterSeq_four : Squarefree (sylvesterSeq 4) := by
  decide +kernel

/-- Every term of Sylvester's sequence is at least $2$. -/
@[category API, AMS 11]
theorem two_le_sylvesterSeq (n : ℕ) : 2 ≤ sylvesterSeq n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [sylvesterSeq]
    have hsq : 2 * sylvesterSeq n ≤ sylvesterSeq n ^ 2 := by nlinarith
    omega

/-- Euclid-product characterization $s_n = 1 + \prod_{k < n} s_k$ for all $n \ge 0$. -/
@[category API, AMS 11]
theorem sylvesterSeq_eq_one_add_prod (n : ℕ) :
    sylvesterSeq n = 1 + ∏ k ∈ Finset.range n, sylvesterSeq k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_comm]
    have hs : 2 ≤ sylvesterSeq n := two_le_sylvesterSeq n
    have hsq : sylvesterSeq n ≤ sylvesterSeq n ^ 2 := by nlinarith
    have hp : ∏ k ∈ Finset.range n, sylvesterSeq k = sylvesterSeq n - 1 := by omega
    change sylvesterSeq n ^ 2 - sylvesterSeq n + 1 =
      1 + sylvesterSeq n * ∏ k ∈ Finset.range n, sylvesterSeq k
    rw [hp, Nat.mul_sub_one, ← sq]
    omega

/-- Distinct entries of `sylvesterSeq` are pairwise coprime, since $s_i \mid s_j - 1$ whenever
$i < j$. -/
@[category API, AMS 11]
theorem sylvesterSeq_pairwise_coprime : Pairwise (Function.onFun Nat.Coprime sylvesterSeq) := by
  have hlt : ∀ {i j : ℕ}, i < j → Nat.Coprime (sylvesterSeq i) (sylvesterSeq j) := by
    intro i j hij
    rw [sylvesterSeq_eq_one_add_prod j]
    obtain ⟨c, hc⟩ : sylvesterSeq i ∣ ∏ k ∈ Finset.range j, sylvesterSeq k :=
      Finset.dvd_prod_of_mem sylvesterSeq (Finset.mem_range.mpr hij)
    rw [hc, Nat.coprime_iff_gcd_eq_one]
    set g := (sylvesterSeq i).gcd (1 + sylvesterSeq i * c)
    rcases Nat.gcd_dvd_left (sylvesterSeq i) (1 + sylvesterSeq i * c) with ⟨x, hx⟩
    rcases Nat.gcd_dvd_right (sylvesterSeq i) (1 + sylvesterSeq i * c) with ⟨y, hy⟩
    change sylvesterSeq i = g * x at hx
    change 1 + sylvesterSeq i * c = g * y at hy
    have hassoc : sylvesterSeq i * c = g * (x * c) := by rw [hx, mul_assoc]
    rcases le_or_gt y (x * c) with hle | hgt
    · have hmul : g * y ≤ g * (x * c) := Nat.mul_le_mul_left g hle
      omega
    · have hmul : g * (x * c) + g ≤ g * y := by
        simpa [Nat.mul_add, mul_one] using Nat.mul_le_mul_left g hgt
      have hg0 : g ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hy
        omega
      omega
  intro i j hij
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt h
  · exact (hij rfl).elim
  · exact (hlt h).symm

/--
Sylvester's telescoping Egyptian-fraction identity `[Sy1880]`: for every $n \ge 0$,
$$\sum_{k=0}^{n-1} \frac{1}{s_k} = 1 - \frac{1}{s_n - 1}.$$
-/
@[category textbook, AMS 11]
theorem sum_inv_sylvesterSeq (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℚ) / sylvesterSeq k =
      1 - 1 / ((sylvesterSeq n : ℚ) - 1) := by
  induction n with
  | zero => norm_num [sylvesterSeq]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hs : 2 ≤ sylvesterSeq n := two_le_sylvesterSeq n
    have hsq : sylvesterSeq n ≤ sylvesterSeq n ^ 2 := by nlinarith
    have hrec : (sylvesterSeq (n + 1) : ℚ) - 1 =
        (sylvesterSeq n : ℚ) * ((sylvesterSeq n : ℚ) - 1) := by
      simp only [sylvesterSeq]
      push_cast [hsq]
      ring
    have hne0 : (sylvesterSeq n : ℚ) ≠ 0 := by
      exact_mod_cast (show sylvesterSeq n ≠ 0 by omega)
    have hne1 : (sylvesterSeq n : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ (sylvesterSeq n : ℚ) := by exact_mod_cast hs
      linarith
    rw [hrec]
    field_simp
    ring

/--
No term of Sylvester's sequence is a perfect power $k^m$ with $k, m > 1$ `[MN24]`.
-/
@[category research solved, AMS 11]
theorem sylvesterSeq_not_isPerfectPower (n : ℕ) : ¬ (sylvesterSeq n).IsPerfectPower := by
  sorry

/--
Is every term $s_n$ of Sylvester's sequence squarefree (`[GKP89, Research Problem 4.65]`,
`[Va91]`)?
-/
@[category research open, question, AMS 11]
theorem sylvester_sequence_squarefree : ∀ n : ℕ, Squarefree (sylvesterSeq n) := by
  sorry

end SylvesterSequence
