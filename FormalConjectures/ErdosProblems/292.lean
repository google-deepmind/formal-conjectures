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
# Erdős Problem 292

*References:*
- [erdosproblems.com/292](https://www.erdosproblems.com/292)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ma00] Martin, Greg, *Denser Egyptian fractions*. Acta Arith. (2000), 231-260.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos292

/-- The set $A$ of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. -/
def A : Set ℕ :=
  {n | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ ∑ m ∈ S, (1 : ℚ) / m = 1}

/--
Let $A$ be the set of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. Explore $A$. In particular, does $A$ have density $1$?

Straus observed that $A$ is closed under multiplication. Furthermore, it is easy to see that $A$
does not contain any prime power.

The answer is yes, as proved by Martin [Ma00], who in fact proved that if
$B=\mathbb{N}\backslash A$ then, for all large $x$,
$$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x},$$
and also gave an essentially complete description of $B$ as those integers which are small
multiples of prime powers.

van Doorn has observed that if $n\in A$ (with $n>1$) then $2n\in A$ also, since if
$\sum \frac{1}{m_i}=1$ then $\frac{1}{2}+\sum\frac{1}{2m_i}=1$ also.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos292.lean#L116"]
theorem erdos_292 : answer(True) ↔ A.HasDensity 1 := by
  sorry

/-- Martin [Ma00] proved that if $B=\mathbb{N}\backslash A$ then
$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x}$. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.martin :
    (fun x : ℕ ↦ ((Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x) =Θ[atTop]
      fun x ↦ Real.log (Real.log x) / Real.log x := by
  sorry

/-- Straus observed that $A$ is closed under multiplication. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.mul : ∀ m ∈ A, ∀ n ∈ A, m * n ∈ A := by
  sorry

/-- $A$ does not contain any prime power. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.prime_pow : ∀ n ∈ A, ¬ IsPrimePow n := by
  sorry

/-- van Doorn observed that if $n\in A$ (with $n>1$) then $2n\in A$ also. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.two_mul : ∀ n ∈ A, 1 < n → 2 * n ∈ A := by
  rintro n ⟨S, hS, hn, hsum⟩ hn1
  have hpos : ∀ m ∈ S, 0 < m := fun m hm => (Finset.mem_Icc.mp (hS hm)).1
  have h1 : 1 ∉ S := by
    intro h
    have hsub : ({1, n} : Finset ℕ) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h
      · rwa [Finset.mem_singleton.mp hx]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun m : ℕ => (1 : ℚ) / m) (fun i _ _ => by positivity)
    rw [Finset.sum_pair (by omega)] at hle
    have : (0 : ℚ) < 1 / n := by
      have : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at hle
    linarith
  refine ⟨insert 2 (S.image (2 * ·)), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have := hpos n hn
      simp only [Finset.mem_Icc]
      omega
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have := (Finset.mem_Icc.mp (hS hm)).2
      have := hpos m hm
      simp only [Finset.mem_Icc]
      omega
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  · have h2 : (2 : ℕ) ∉ S.image (2 * ·) := by
      intro h
      obtain ⟨m, hm, hm2⟩ := Finset.mem_image.mp h
      exact h1 (by rwa [show m = 1 by omega] at hm)
    rw [Finset.sum_insert h2, Finset.sum_image (fun a _ b _ h => by omega)]
    have : ∑ m ∈ S, (1 : ℚ) / ((2 * m : ℕ) : ℚ) = (1 / 2) * ∑ m ∈ S, (1 : ℚ) / m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      rw [one_div_mul_one_div_rev]
      ring_nf
    rw [this, hsum]
    norm_num

end Erdos292
