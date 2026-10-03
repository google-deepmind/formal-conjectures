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
# Erdős Problem 411

*References:*
- [erdosproblems.com/411](https://www.erdosproblems.com/411)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p. 81.
- [OEIS A383044](https://oeis.org/A383044): numbers $m$ with $\phi(m) + \phi(m + \phi(m)) = m$.
-/

namespace Erdos411

open Filter Nat

/-- The map $g(n) = n + \phi(n)$. -/
def g (n : ℕ) : ℕ := n + φ n

/--
Let $g_1=g(n)=n+\phi(n)$ and $g_k(n)=g(g_{k-1}(n))$. For which $n$ and $r$ is it true that
$g_{k+r}(n)=2g_k(n)$ for all large $k$?

Here `g^[k]` is the $k$-fold iterate of `g`. The known solutions with $r = 2$ include $n = 10$ and
$n = 94$ (see `erdos_411.variants.ten` and `erdos_411.variants.ninety_four`); more generally
$n = 2^l p$ with $l \geq 1$ and $p \in \{2, 3, 5, 7, 35, 47\}$. Steinerberger observed that for
$r = 2$ the condition is equivalent to $\phi(n) + \phi(n + \phi(n)) = n$ (OEIS A383044).
-/
@[category research open, AMS 11]
theorem erdos_411 :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ ∀ᶠ k in atTop, g^[k + p.2] p.1 = 2 * g^[k] p.1} =
      answer(sorry) := by
  sorry

/--
Cambie conjectures (comments on the problem page) that the only solutions have $r = 2$ and
$n = 2^l p$ for some $l \geq 1$ and $p \in \{2, 3, 5, 7, 35, 47\}$.
-/
@[category research open, AMS 11]
theorem erdos_411.variants.cambie : answer(sorry) ↔
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ ∀ᶠ k in atTop, g^[k + p.2] p.1 = 2 * g^[k] p.1} =
      {p : ℕ × ℕ | p.2 = 2 ∧
        ∃ l, 1 ≤ l ∧ ∃ q ∈ ({2, 3, 5, 7, 35, 47} : Finset ℕ), p.1 = 2 ^ l * q} := by
  sorry

/-- If `a` is even then `g (2 * a) = 2 * g a`, since `φ (2 * a) = 2 * φ a` for even `a`. -/
@[category API, AMS 11]
theorem g_two_mul {a : ℕ} (ha : 2 ∣ a) : g (2 * a) = 2 * g a := by
  unfold g
  rw [totient_mul_of_prime_of_dvd prime_two ha]
  ring

/-- For `2 < m`, `g m` is even iff `m` is even, since `φ m` is even. -/
@[category API, AMS 11]
theorem two_dvd_g {m : ℕ} (hm : 2 < m) (h : 2 ∣ m) : 2 ∣ g m := by
  unfold g
  exact Nat.dvd_add h (totient_even hm).two_dvd

/--
If `a` is an even number larger than `2` with `g (g a) = 2 * a`, then `g^[k + 2] a = 2 * g^[k] a`
for every `k`. This produces the known solutions.
-/
@[category API, AMS 11]
theorem iterate_add_two_eq {a : ℕ} (ha : 2 < a) (ha2 : 2 ∣ a) (h2 : g (g a) = 2 * a) (k : ℕ) :
    g^[k + 2] a = 2 * g^[k] a ∧ 2 < g^[k] a ∧ 2 ∣ g^[k] a := by
  induction k with
  | zero => exact ⟨by simp [Function.iterate_succ_apply', h2], ha, ha2⟩
  | succ k ih =>
    obtain ⟨hk, hlt, hdvd⟩ := ih
    have hlt' : 2 < g^[k + 1] a := by
      rw [Function.iterate_succ_apply']
      exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    refine ⟨?_, hlt', ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (n := k), hk, g_two_mul hdvd]
    · rw [Function.iterate_succ_apply']
      exact two_dvd_g hlt hdvd

/-- `n = 10`, `r = 2` is a solution: `g 10 = 14` and `g 14 = 20`. -/
@[category test, AMS 11]
theorem erdos_411.variants.ten : ∀ k, g^[k + 2] 10 = 2 * g^[k] 10 := fun k =>
  (iterate_add_two_eq (a := 10) (by norm_num) (by norm_num) (by decide) k).1

/-- `n = 94`, `r = 2` is a solution: `g 94 = 140` and `g 140 = 188`. -/
@[category test, AMS 11]
theorem erdos_411.variants.ninety_four : ∀ k, g^[k + 2] 94 = 2 * g^[k] 94 := fun k =>
  (iterate_add_two_eq (a := 94) (by norm_num) (by norm_num) (by decide) k).1

end Erdos411
