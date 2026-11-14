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
# Erdős Problem 436

*References:*
- [erdosproblems.com/436](https://www.erdosproblems.com/436)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [LeLe62] Lehmer, D. H. and Lehmer, Emma, *On runs of residues*. Proc. Amer. Math. Soc. (1962),
  102-106.
- [LLMS62] Lehmer, D. H. and Lehmer, E. and Mills, W. H. and Selfridge, J. L., *Machine proof of a
  theorem on cubic residues*. Math. Comp. (1962), 407-415.
- [BiMi63] Bierstedt, R. G. and Mills, W. H., *On the bound for a pair of consecutive quartic
  residues of a prime*. Proc. Amer. Math. Soc. (1963), 628-632.
- [LLM63] Lehmer, D. H. and Lehmer, Emma and Mills, W. H., *Pairs of consecutive power residues*.
  Canadian J. Math. (1963), 172-177.
- [BLL64] Brillhart, John and Lehmer, D. H. and Lehmer, Emma, *Bounds for pairs of consecutive
  seventh and higher power residues*. Math. Comp. (1964), 397-407.
- [Gr64g] Graham, R. L., *On quadruples of consecutive $k$th power residues*. Proc. Amer. Math.
  Soc. (1964), 196-197.
- [Du65] Dunton, M., *Bounds for pairs of cubic residues*. Proc. Amer. Math. Soc. (1965),
  330-332.
- [Hi91] Hildebrand, Adolf, *On consecutive $k$th power residues. II*. Michigan Math. J. (1991),
  241-253.
-/

@[expose] public section

open Filter

namespace Erdos436

/-- `IsPowerResidue k p a` means that $a$ is a $k$th power residue modulo $p$, that is,
$p \nmid a$ and $a \equiv x^k \pmod{p}$ for some $x$. -/
def IsPowerResidue (k p a : ℕ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ ∃ x : ZMod p, x ^ k = a

/-- `r k m p` is the least $r \geq 1$ such that $r, r + 1, \ldots, r + m - 1$ are all $k$th
power residues modulo $p$, or `⊤` if there is no such $r$. -/
noncomputable def r (k m p : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ ∀ i < m, IsPowerResidue k p (n + i)), (n : ℕ∞)

/-- $\Lambda(k, m) = \limsup_{p \to \infty} r(k, m, p)$, where $p$ runs over the primes. -/
noncomputable def runLimsup (k m : ℕ) : ℕ∞ :=
  limsup (r k m) (atTop ⊓ 𝓟 {p | p.Prime})

@[inherit_doc] local notation "Λ" => runLimsup

/--
If $p$ is a prime and $k, m \geq 2$, let $r(k, m, p)$ be the minimal $r$ such that
$r, r + 1, \ldots, r + m - 1$ are all $k$th power residues modulo $p$, and let
$\Lambda(k, m) = \limsup_{p \to \infty} r(k, m, p)$. Is $\Lambda(k, 2)$ finite for all $k$?

A question of Lehmer and Lehmer [LeLe62]. Hildebrand [Hi91] proved that $\Lambda(k, 2)$ is finite
for all $k \geq 2$.
-/
@[category research solved, question, AMS 11]
theorem erdos_436.parts.i : ∀ k ≥ 2, Λ k 2 < ⊤ := by
  sorry

/--
Is $\Lambda(k, 3)$ finite for all odd $k$?

Lehmer, Lehmer, Mills and Selfridge [LLMS62] proved $\Lambda(3, 3) = 23532$. The question is open
for odd $k \geq 5$.
-/
@[category research open, question, AMS 11]
theorem erdos_436.parts.ii : ∀ k ≥ 3, Odd k → Λ k 3 < ⊤ := by
  sorry

/-- Lehmer and Lehmer [LeLe62] proved $\Lambda(2, 2) = 9$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.two_two : Λ 2 2 = 9 := by
  sorry

/-- Dunton [Du65] proved $\Lambda(3, 2) = 77$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.three_two : Λ 3 2 = 77 := by
  sorry

/-- Bierstedt and Mills [BiMi63] proved $\Lambda(4, 2) = 1224$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.four_two : Λ 4 2 = 1224 := by
  sorry

/-- Lehmer, Lehmer and Mills [LLM63] proved $\Lambda(5, 2) = 7888$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.five_two : Λ 5 2 = 7888 := by
  sorry

/-- Lehmer, Lehmer and Mills [LLM63] proved $\Lambda(6, 2) = 202124$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.six_two : Λ 6 2 = 202124 := by
  sorry

/-- Brillhart, Lehmer and Lehmer [BLL64] proved $\Lambda(7, 2) = 1649375$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.seven_two : Λ 7 2 = 1649375 := by
  sorry

/-- Lehmer, Lehmer, Mills and Selfridge [LLMS62] proved $\Lambda(3, 3) = 23532$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.three_three : Λ 3 3 = 23532 := by
  sorry

/-- The modulus $4 \prod n$ over $1 \le n \le N$ with $3 \nmid n$, used for `even_three`. -/
private def evenThreeModulus (N : ℕ) : ℕ := 4 * ∏ n ∈ Finset.Icc 1 N with ¬ 3 ∣ n, n

@[category API, AMS 11]
private theorem evenThreeModulus_pos (N : ℕ) : 0 < evenThreeModulus N :=
  Nat.mul_pos (by norm_num) (Finset.prod_pos fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    omega)

@[category API, AMS 11]
private theorem coprime_three_evenThreeModulus (N : ℕ) : Nat.Coprime 3 (evenThreeModulus N) := by
  refine Nat.Coprime.mul_right (by decide) (Nat.Coprime.prod_right fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn.2

/-- If $p \equiv 3 \pmod{M}$, then $J(n \mid p) = -1$ for $1 \le n \le N$ with
$n \equiv 2 \pmod 3$, by reciprocity modulo $4n$. -/
@[category API, AMS 11]
private theorem jacobiSym_eq_neg_one {N p n : ℕ} (hp : (p : ZMod (evenThreeModulus N)) = 3)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hn3 : n % 3 = 2) : jacobiSym n p = -1 := by
  have hdvd : 4 * n ∣ evenThreeModulus N := mul_dvd_mul_left 4
    (Finset.dvd_prod_of_mem (fun i => i)
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, by omega⟩))
  have hmod : p % (4 * n) = 3 := by
    have h : p ≡ 3 [MOD evenThreeModulus N] :=
      (ZMod.natCast_eq_natCast_iff' p 3 (evenThreeModulus N)).mp (by simpa using hp)
    have h' := Nat.ModEq.of_dvd hdvd h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (show 3 < 4 * n by omega)] at h'
  have hodd : Odd p := by
    have h := Nat.mod_mod_of_dvd p (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩)
    rw [hmod] at h
    exact Nat.odd_iff.mpr (by omega)
  have h2 : ((n : ℕ) : ℤ) % ((3 : ℕ) : ℤ) = 2 := by push_cast; omega
  rw [jacobiSym.mod_right' n hodd, hmod, jacobiSym.mod_left, h2, jacobiSym.at_two (by decide),
    ZMod.χ₈_nat_eq_if_mod_eight]
  norm_num

/-- For even $k$, a $k$th power residue modulo a prime $p$ has $J(n \mid p) \ne -1$. -/
@[category API, AMS 11]
private theorem not_isPowerResidue_of_even {k p n : ℕ} [Fact p.Prime] (hk : Even k)
    (h : jacobiSym n p = -1) : ¬ IsPowerResidue k p n := by
  rintro ⟨-, x, hx⟩
  obtain ⟨t, rfl⟩ := hk
  have hsq : IsSquare ((n : ℤ) : ZMod p) := ⟨x ^ t, by rw [Int.cast_natCast, ← hx, pow_add]⟩
  exact ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp h hsq

/-- For even $k$ and a prime $p \equiv 3 \pmod{M}$, $M$ the modulus for $N + 2$:
$r(k, 3, p) \ge N$. -/
@[category API, AMS 11]
private theorem le_r_of_even {k N p : ℕ} (hk : Even k) (hp : p.Prime)
    (hpM : (p : ZMod (evenThreeModulus (N + 2))) = 3) : (N : ℕ∞) ≤ r k 3 p := by
  have := Fact.mk hp
  refine le_iInf₂ fun n hn => ?_
  obtain ⟨hn1, hres⟩ := hn
  by_contra hlt
  have hnN : n < N := by exact_mod_cast not_le.mp hlt
  obtain ⟨i, hi, hi3⟩ : ∃ i < 3, (n + i) % 3 = 2 := by
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · exact ⟨2, by norm_num, by omega⟩
    · exact ⟨1, by norm_num, by omega⟩
    · exact ⟨0, by norm_num, by omega⟩
  exact not_isPowerResidue_of_even hk
    (jacobiSym_eq_neg_one hpM (by omega) (by omega) hi3) (hres i hi)

/-- Lehmer and Lehmer [LeLe62] proved $\Lambda(k, 3) = \infty$ for all even $k$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.even_three : ∀ k ≥ 2, Even k → Λ k 3 = ⊤ := by
  intro k _ hk
  refine ENat.eq_top_iff_forall_ge.mpr fun N => ?_
  unfold runLimsup
  apply le_limsup_of_frequently_le'
  rw [frequently_inf_principal, frequently_atTop]
  intro a
  have : NeZero (evenThreeModulus (N + 2)) := NeZero.of_pos (evenThreeModulus_pos _)
  have hunit : IsUnit ((3 : ℕ) : ZMod (evenThreeModulus (N + 2))) :=
    (ZMod.isUnit_iff_coprime 3 _).mpr (coprime_three_evenThreeModulus _)
  -- Dirichlet: arbitrarily large primes `p ≡ 3 (mod M)`.
  obtain ⟨p, hpa, hp, hpM⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit a
  exact ⟨p, hpa.le, hp, le_r_of_even hk hp (by simpa using hpM)⟩

/-- Graham [Gr64g] proved $\Lambda(k, l) = \infty$ for all $k \geq 2$ and $l \geq 4$. -/
@[category research solved, AMS 11]
theorem erdos_436.variants.ge_four : ∀ k ≥ 2, ∀ l ≥ 4, Λ k l = ⊤ := by
  sorry

/-- Modulo $13$, the quadratic residues are $1, 3, 4, 9, 10, 12$, so the first pair of
consecutive quadratic residues starts at $3$. -/
@[category test, AMS 11]
theorem r_two_two_thirteen : r 2 2 13 = 3 := by
  have h2 : ¬ IsPowerResidue 2 13 2 := by
    unfold IsPowerResidue
    decide
  apply le_antisymm
  · refine iInf₂_le 3 ⟨by norm_num, ?_⟩
    intro i hi
    interval_cases i
    · exact ⟨by decide, 4, by decide⟩
    · exact ⟨by decide, 2, by decide⟩
  · refine le_iInf₂ ?_
    rintro n ⟨hn, h⟩
    have : 3 ≤ n := by
      by_contra hlt
      interval_cases n
      · exact h2 (h 1 (by norm_num))
      · exact h2 (h 0 (by norm_num))
    exact_mod_cast this

end Erdos436
