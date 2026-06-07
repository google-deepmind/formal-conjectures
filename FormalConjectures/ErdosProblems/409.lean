/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 409

*Reference:* [erdosproblems.com/409](https://www.erdosproblems.com/409)
-/

open scoped Topology ArithmeticFunction.sigma Nat
open Filter

namespace Erdos409

/--
How many iterations of $n\mapsto\phi(n) + 1$ are needed before a prime is reached?
-/
-- Formalisation note: the sequence of iterates always terminates if `n > 0`
-- since it is strictly decreasing unless the input is prime, at which point
-- it becomes static. See also https://oeis.org/A39651
@[category research open, AMS 11]
theorem erdos_409.parts.i (n : ℕ) (hn : 0 < n) :
    IsLeast { i | (φ · + 1)^[i] n |>.Prime } answer(sorry) := by
  sorry

/-- If $n > 0$, then the iteration $n\mapsto\phi(n) + 1$ necessarily
reaches a prime. -/
@[category test, AMS 11]
theorem erdos_409.variants.termination (n : ℕ) (hn : 0 < n) :
    ∃ i, (φ · + 1)^[i] n |>.Prime := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · -- already prime: zero iterations suffice
      exact ⟨0, by simpa using hp⟩
    · rcases Nat.lt_or_ge n 2 with h2 | hn2
      · -- `n = 1`: one step gives `φ 1 + 1 = 2`, which is prime
        obtain rfl : n = 1 := by omega
        exact ⟨1, by simp [Nat.totient_one, Nat.prime_two]⟩
      · -- `n ≥ 2` and composite, so `φ n + 1 < n`; recurse on it
        have hlt : φ n + 1 < n := by
          have hφ : φ n < n := Nat.totient_lt n hn2
          have : φ n ≠ n - 1 := fun he => hp ((Nat.totient_eq_iff_prime hn).mp he)
          omega
        obtain ⟨j, hj⟩ := ih (φ n + 1) hlt (by omega)
        exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

-- Formalisation note: it's possible that solution to `erdos_409.parts.i` needs to be
-- expressed asymptotically. To handle this we include `IsTheta`, `IsBigO`
-- and `IsLittleO` variants below. Since a solution is not known this necessitates
-- the use of an `answer(sorry)` placeholder. Trivial or sub-optimal solutions
-- will therefore exist to the asymptotic formalisations. A true solution to
-- the asymptotic variants should have a degree of optimality or non-triviality to it.
/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\phi(n) + 1$ before a prime
is reached. What is $\Theta(c(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.i.isTheta (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\phi(n) + 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = O(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.i.isBigO (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\phi(n) + 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = o(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.i.isLittleO (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\phi(n) + 1$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.ii :
    answer(sorry) ↔ ∃ (p : ℕ) (hp : p.Prime), { n | ∃ i, (φ · + 1)^[i] n = p }.Infinite := by
  sorry

/--
What is the density of $n$ which reach any fixed prime under the iteration $n\mapsto\phi(n) + 1$?
-/
@[category research open, AMS 11]
theorem erdos_409.parts.iii (p : ℕ) (h : p.Prime) (α : ℝ)
    (hα : { n | ∃ i, (φ · + 1)^[i] n = p }.HasDensity α) :
    α = answer(sorry) := by
  sorry

/--
How many iterations of $n\mapsto\sigma(n) - 1$ are needed before a prime is reached?
-/
-- Formalisation note: non-termination of this sequence is less clear since
-- it is strictly increasing except at primes.
@[category research open, AMS 11]
theorem erdos_409.variants.sigma (n : ℕ) (hn : n > 1) :
    IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } answer(sorry) := by
  sorry

/-- If $n > 1$ then the iteration $n\mapsto\sigma(n) - 1$ necessarily reaches a prime.
Note: this is open — it is not clear that the σ iteration always terminates,
since it is non-decreasing (unlike the φ iteration which is strictly decreasing). -/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma_termination (n : ℕ) (hn : n > 1) :
    ∃ i, (σ 1 · - 1)^[i] n |>.Prime := by
  sorry

-- Formalisation note: See the above formalisation note for the rationale
-- for including asymptotic variants
/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\sigma(n) - 1$ before a prime
is reached. What is $\Theta(c(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma_isTheta (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\sigma(n) - 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = O(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma_isBigO (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $c(n)$ be the minimum number of iterations of $n\mapsto\sigma(n) - 1$ before a prime
is reached. Find the simplest function $g(n)$ such that $c(n) = o(g(n))$?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma_isLittleO (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Is it true that iterates of $n\mapsto\sigma(n) - 1$ always reach a prime?
-/
@[category research open, AMS 11]
theorem erdos_409.variants.sigma_prime_termination :
    answer(sorry) ↔ ∀ n > 1, ∃ i, (σ 1 · - 1)^[i] n |>.Prime := by
  sorry

-- ## Partial result: `c(n) = O(√n)`
--
-- The following lemmas establish an honest upper bound on the iteration count
-- for the φ-iteration: the number of steps to reach a prime is `O(√n)`.
-- This is NOT a solution to the open problem `erdos_409.parts.i` (which asks for
-- the exact / tight asymptotic), only a correct upper bound.

open Finset in
/-- For `m ≥ 2`, the totient drops by at least `m / m.minFac`:
`φ m ≤ m - m / m.minFac`. -/
@[category API, AMS 11]
theorem erdos_409.aux.totient_le_sub_div_minFac (m : ℕ) (hm : 2 ≤ m) :
    φ m ≤ m - m / m.minFac := by
  classical
  set p := m.minFac with hp
  have hp2 : 2 ≤ p := (Nat.minFac_prime (by omega)).two_le
  have hpdvd : p ∣ m := Nat.minFac_dvd m
  have hppos : 0 < p := by omega
  -- The multiples `k * p` for `k < m / p` are non-coprime to `m` and lie in `range m`.
  have hinj : (m / p) ≤ #((range m).filter (fun a => ¬ m.Coprime a)) := by
    have hmaps : Set.MapsTo (fun k => k * p) (range (m / p) : Set ℕ)
        ((range m).filter (fun a => ¬ m.Coprime a) : Set ℕ) := by
      intro k hk
      simp only [coe_range, Set.mem_Iio] at hk
      simp only [coe_filter, mem_range, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · calc k * p < (m / p) * p := by
              exact (Nat.mul_lt_mul_right hppos).mpr hk
            _ ≤ m := Nat.div_mul_le_self m p
      · -- `gcd m (k*p) ≥ p > 1` since `p ∣ m` and `p ∣ k*p`
        intro hcop
        have : p ∣ Nat.gcd m (k * p) := Nat.dvd_gcd hpdvd ⟨k, by ring⟩
        rw [hcop] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
    have hinjOn : Set.InjOn (fun k => k * p) (range (m / p) : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hppos hab
    have := Finset.card_le_card_of_injOn (fun k => k * p) hmaps hinjOn
    simpa using this
  have hsum := Finset.card_filter_add_card_filter_not (s := range m) (fun a => m.Coprime a)
  rw [Nat.totient_eq_card_coprime]
  simp only [card_range] at hsum
  omega

/-- For composite `m ≥ 2`, one step of the φ-iteration drops `m` by at least
`Nat.sqrt m`: `φ m + 1 ≤ m - Nat.sqrt m + 1`, equivalently `φ m + Nat.sqrt m ≤ m`. -/
@[category API, AMS 11]
theorem erdos_409.aux.totient_add_sqrt_le (m : ℕ) (hm : 2 ≤ m) (hc : ¬ m.Prime) :
    φ m + Nat.sqrt m ≤ m := by
  set p := m.minFac with hp
  have hsq : p ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hc
  -- `Nat.sqrt m ≤ m / p`, since `p ≤ Nat.sqrt m` would need care; use `p^2 ≤ m`.
  have hsqrt_le : Nat.sqrt m ≤ m / p := by
    -- `p ≤ Nat.sqrt m` from `p^2 ≤ m`, then `Nat.sqrt m ≤ m / Nat.sqrt m ≤ m / p`?
    -- Direct: `Nat.sqrt m * p ≤ m`? We instead show `Nat.sqrt m ≤ m / p` via `Nat.le_div_iff`.
    have hp_le : p ≤ Nat.sqrt m := by
      rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := by ring
        _ ≤ m := hsq
    have hppos : 0 < p := by
      have := (Nat.minFac_prime (show m ≠ 1 by omega)).two_le; omega
    rw [Nat.le_div_iff_mul_le hppos]
    calc Nat.sqrt m * p ≤ Nat.sqrt m * Nat.sqrt m := by
          exact Nat.mul_le_mul_left _ hp_le
      _ ≤ m := Nat.sqrt_le m
  have hdrop : φ m ≤ m - m / p := erdos_409.aux.totient_le_sub_div_minFac m hm
  have hdpos : m / p ≤ m := Nat.div_le_self m p
  omega

/-- The iteration `n ↦ φ n + 1` reaches a prime within `6 * Real.sqrt n` steps
(a real-valued bound, which makes the per-step descent argument clean). -/
@[category API, AMS 11]
theorem erdos_409.aux.iter_count_le_sqrt (n : ℕ) (hn : 0 < n) :
    ∃ i, ((φ · + 1)^[i] n).Prime ∧ (i : ℝ) ≤ 6 * Real.sqrt n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · refine ⟨0, by simpa using hp, ?_⟩
      simp only [Nat.cast_zero]
      positivity
    · rcases Nat.lt_or_ge n 9 with h9 | hn9
      · -- small `n`: terminate directly, count is at most `1`, and `1 ≤ 6√n` for `n ≥ 1`.
        have hsmall : ∃ i ≤ 1, ((φ · + 1)^[i] n).Prime := by
          interval_cases n <;> simp_all <;>
            first
            | exact ⟨0, by norm_num, by decide⟩
            | exact ⟨1, by norm_num, by decide⟩
        obtain ⟨i, hi1, hip⟩ := hsmall
        refine ⟨i, hip, ?_⟩
        have h1n : (1 : ℝ) ≤ Real.sqrt n := by
          have h1le : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          calc (1 : ℝ) = Real.sqrt 1 := by rw [Real.sqrt_one]
            _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1le
        have hi1' : (i : ℝ) ≤ 1 := by exact_mod_cast hi1
        nlinarith [Real.sqrt_nonneg (n : ℝ), hi1', h1n]
      · -- composite, `n ≥ 9`
        have hn2 : 2 ≤ n := by omega
        have hstep : φ n + Nat.sqrt n ≤ n := erdos_409.aux.totient_add_sqrt_le n hn2 hp
        have hsqrt_pos : 1 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
        have hlt : φ n + 1 < n := by
          have hφ : φ n < n := Nat.totient_lt n hn2
          have : φ n ≠ n - 1 := fun he => hp ((Nat.totient_eq_iff_prime hn).mp he)
          omega
        obtain ⟨j, hjp, hj⟩ := ih (φ n + 1) hlt (by omega)
        refine ⟨j + 1, by rwa [Function.iterate_succ_apply], ?_⟩
        set g : ℕ := φ n + 1 with hg
        -- Real facts about the descent
        have hgle : (g : ℝ) ≤ (n : ℝ) - Real.sqrt n + 2 := by
          have hns : (Nat.sqrt n : ℝ) ≥ Real.sqrt n - 1 := by
            have hlt : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
              have hns := Nat.lt_succ_sqrt n
              have : n < (Nat.sqrt n + 1) ^ 2 := by rw [Nat.pow_two]; exact hns
              calc (n : ℝ) < (((Nat.sqrt n + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
                _ = ((Nat.sqrt n : ℝ) + 1) ^ 2 := by push_cast; ring
            have : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
              rw [show Real.sqrt n = Real.sqrt (n : ℝ) from rfl]
              calc Real.sqrt (n : ℝ) < Real.sqrt (((Nat.sqrt n : ℝ) + 1) ^ 2) :=
                    Real.sqrt_lt_sqrt (by positivity) hlt
                _ = (Nat.sqrt n : ℝ) + 1 := by
                    rw [Real.sqrt_sq (by positivity)]
            linarith
          have hgsub : (g : ℝ) ≤ (n : ℝ) - (Nat.sqrt n : ℝ) + 1 := by
            have : g + Nat.sqrt n ≤ n + 1 := by omega
            have hr : ((g + Nat.sqrt n : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at hr; linarith
          linarith
        -- √n - √g ≥ 1/3, using n ≥ 9
        have hsqrtn3 : Real.sqrt n ≥ 3 := by
          have h9le : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
          have : Real.sqrt 9 ≤ Real.sqrt n := Real.sqrt_le_sqrt h9le
          rwa [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
        have hgpos : (0 : ℝ) ≤ (g : ℝ) := by positivity
        have hgnn : (g : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : g ≤ n)
        have hsq_g : Real.sqrt g ≤ Real.sqrt n := Real.sqrt_le_sqrt hgnn
        have hkey : Real.sqrt n - Real.sqrt g ≥ 1 / 6 := by
          have hdiff : (n : ℝ) - g ≥ Real.sqrt n - 2 := by linarith
          have hfactor : (n : ℝ) - g = (Real.sqrt n - Real.sqrt g) * (Real.sqrt n + Real.sqrt g) := by
            have e1 : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
              Real.mul_self_sqrt (by positivity)
            have e2 : Real.sqrt g * Real.sqrt g = (g : ℝ) :=
              Real.mul_self_sqrt hgpos
            ring_nf
            nlinarith [e1, e2]
          have hsumpos : Real.sqrt n + Real.sqrt g ≤ 2 * Real.sqrt n := by linarith
          have hsumpos' : 0 < Real.sqrt n + Real.sqrt g := by
            have : 0 < Real.sqrt n := by linarith
            have : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
            linarith
          -- (√n-√g) = (n-g)/(√n+√g) ≥ (√n-2)/(2√n) ≥ 1/6 since √n ≥ 3
          have hge : Real.sqrt n - Real.sqrt g ≥ (Real.sqrt n - 2) / (2 * Real.sqrt n) := by
            rw [ge_iff_le, div_le_iff₀ (by linarith)]
            nlinarith [hfactor, hdiff, hsq_g, Real.sqrt_nonneg (g:ℝ)]
          have hlb : (Real.sqrt n - 2) / (2 * Real.sqrt n) ≥ 1 / 6 := by
            rw [ge_iff_le, le_div_iff₀ (by linarith)]
            nlinarith [hsqrtn3]
          linarith
        have hjr : (j : ℝ) ≤ 6 * Real.sqrt g := hj
        have : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [this]
        linarith [hkey, hjr]

open Asymptotics in
/-- **Partial result.** The φ-iteration count is `O(√n)`. This is an honest upper
bound, not a solution to the open exact-asymptotic problem `erdos_409.parts.i`. -/
@[category research solved, AMS 11]
theorem erdos_409.variants.isBigO_sqrt (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (fun n => Real.sqrt n) := by
  rw [isBigO_iff]
  refine ⟨6, ?_⟩
  rw [eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < n := hn
  obtain ⟨i, hip, hi⟩ := erdos_409.aux.iter_count_le_sqrt n hnpos
  have hle : c n ≤ i := (h n hnpos).2 hip
  have hcn : (c n : ℝ) ≤ (i : ℝ) := by exact_mod_cast hle
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith

end Erdos409
