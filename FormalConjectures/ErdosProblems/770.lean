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
# Erdős Problem 770

*References:*
 - [erdosproblems.com/770](https://www.erdosproblems.com/770)
 - [Er74b] Erdős, P., [*Remarks on some problems in number theory*](https://www.renyi.hu/~p_erdos/1974-27.pdf),
   Mathematica Balkanica 4 (1974), 197–202, §II.
 - [Ma26] MacKenzie, D., [*The large-prime threshold in Erdős Problem 770(iii)*](https://doi.org/10.5281/zenodo.24409350),
   Theorem 1 (2026).
 - [MTT16] McGown, K., Treviño, E., and Trudgian, T.,
   [*Resolving Grosswald's conjecture on GRH*](https://arxiv.org/abs/1508.05182), Theorem 2.
 - [Su26] Sutherland, A., [*Verification files for the Lean proof of the Riemann Hypothesis*](https://math.mit.edu/~drew/grh/).
-/

@[expose] public section

open Set ENat Filter

namespace Erdos770


/-- Let $h n$ be the minimal number such that $2 ^ n - 1, \dots, h(n) ^ n - 1$
are collectively coprime. -/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

/-- `n + 1` is prime iff `h n = n + 1`. This is described as 'easy to see' in [Er74b]. -/
@[category textbook, AMS 11]
theorem Nat.Prime.h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := by
  sorry

/-- For odd `n`, the values of `h n` form an unbounded set.
This is described as 'easy to see' in [Er74b]. -/
@[category textbook, AMS 11]
theorem erdos_770.variants.odd_h_unbounded : Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd)):= by
  sorry


/-- For every prime `p`, does the density of integers with `h n = p` exist? -/
@[category research open, question, AMS 11]
theorem erdos_770.parts.i : ∀ p : ℕ, p.Prime → ∃ a, HasDensity {n | h n = p} a := by
  sorry

/-- Does `liminf h n = ∞`? -/
@[category research open, question, AMS 11]
theorem erdos_770.parts.ii : liminf h atTop = ⊤ := by
  sorry

/-- If $p$ is prime and $p-1$ divides $n$, then Fermat's little theorem gives
$p \mid a^n-1$ for every $2 \le a < p$. Hence $p \le h(n)$. -/
@[category API, AMS 11]
theorem prime_le_h_of_sub_one_dvd {n p : ℕ} (hp : p.Prime) (hd : p - 1 ∣ n) :
    (p : ℕ∞) ≤ h n := by
  refine le_sInf fun m ⟨_, hm⟩ ↦ ?_
  by_contra! hmp
  lift m to ℕ using ne_top_of_lt hmp
  have hmp' : m < p := by exact_mod_cast hmp
  have hdvd : p ∣ ((Finset.Icc 2 m).image fun a ↦ a ^ n - 1).gcd id := by
    simp only [Finset.dvd_gcd_iff, Finset.forall_mem_image, id_eq]
    intro a ha
    obtain ⟨ha₂, ham⟩ := Finset.mem_Icc.mp ha
    have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0 < a)
      (by omega : a < p))).symm
    obtain ⟨k, rfl⟩ := hd
    have hpow := (Nat.ModEq.pow_totient hcop).pow k
    rw [Nat.totient_prime hp, ← pow_mul, one_pow] at hpow
    exact hpow.symm.dvd'
  exact hp.not_dvd_one (hm ▸ hdvd)

/-- To get equality in the prime lower bound it suffices to exclude larger primes from the gcd
at the cutoff $p$. This is the arithmetic step used in [Ma26, §3]. -/
@[category API, AMS 11]
theorem h_eq_prime_of_excludes_larger {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hp₂ : 2 < p)
    (hd : p - 1 ∣ n) (hex : ∀ q : ℕ, q.Prime → p < q →
      ∃ a ∈ Finset.Icc 2 p, ¬ q ∣ a ^ n - 1) : h n = p := by
  refine le_antisymm (sInf_le ⟨by exact_mod_cast hp₂, ?_⟩) (prime_le_h_of_sub_one_dvd hp hd)
  change ((Finset.Icc 2 p).image fun a ↦ a ^ n - 1).gcd id = 1
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hdiv
  have hall : ∀ a ∈ Finset.Icc 2 p, q ∣ a ^ n - 1 := by
    simpa only [Finset.dvd_gcd_iff, Finset.forall_mem_image, id_eq] using hdiv
  rcases le_or_gt q p with hqp | hpq
  · have hpower := dvd_pow_self q hn
    have hpred := hall q (Finset.mem_Icc.mpr ⟨hq.two_le, hqp⟩)
    have hdiff : q ^ n - (q ^ n - 1) = 1 := by
      have := pow_pos hq.pos n
      omega
    exact hq.not_dvd_one (hdiff ▸ Nat.dvd_sub hpower hpred)
  · obtain ⟨a, ha, h⟩ := hex q hq hpq
    exact h (hall a ha)

/-- Is it true that if `p` is the greatest prime such that `p - 1 ∣ n` and `p > n ^ ε`, then
`h n = p`?

MacKenzie [Ma26, Theorem 1] gives an affirmative argument and credits Korsky with the earlier
implication from Dirichlet GRH. For a possible common prime divisor $q > p$, the argument uses
the bound on the least prime primitive root [MTT16] for $q \le n^2$ and counts distinct products
for $q > n^2$. Sutherland [Su26] documents the verification of Alpöge's Dirichlet GRH input. -/
@[category research open, question, AMS 11]
theorem erdos_770.parts.iii : ∀ ε > 0, ∀ᶠ n in atTop,
    let p := sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}
    p > (n : ℝ) ^ (ε : ℝ) → h n = p := by
  sorry

/-- It is probably true that `h n = 3` for infinitely many `n`. -/
@[category research open, AMS 11]
theorem erdos_770.variants.three : {n | h n = 3}.Infinite := by
  sorry

end Erdos770
