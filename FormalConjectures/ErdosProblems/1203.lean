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
# Erdős Problem 1203

*References:*
- [erdosproblems.com/1203](https://www.erdosproblems.com/1203)
- P. Erdős, *A survey of problems in combinatorial number theory*, Ann. Discrete Math.
  **6** (1980), 89–115, [p. 107, equation (4)](https://users.renyi.hu/~p_erdos/1980-03.pdf#page=19).
-/

@[expose] public section

open Filter Real
open scoped ArithmeticFunction.omega

namespace Erdos1203

/-- The logarithmic weight $\log\log t/\log t$. -/
noncomputable def logWeight (t : ℕ) : ℝ := log (log (t : ℝ)) / log (t : ℝ)

/-- Erdős's $f(n,t)$ is the largest number of distinct prime factors among $n+1,\ldots,n+t$. -/
def intervalMax (n t : ℕ) : ℕ := (Finset.Icc 1 t).sup fun i ↦ ω (n + i)

/-- Erdős's $F(n)$, the supremum of $f(n,t)\log\log t/\log t$. The logarithmic
ratio is defined over the reals for integer $t\ge 2$. -/
noncomputable def F (n : ℕ) : ℝ :=
  ⨆ t : {t : ℕ // 2 ≤ t}, (intervalMax n t : ℝ) * logWeight t

/-- The formulation on erdosproblems.com uses $\omega(n+k)$ at the endpoint $k$. -/
noncomputable def endpointF (n : ℕ) : ℝ :=
  ⨆ k : ℕ, (ω (n + k) : ℝ) * logWeight k

/-- Erdős conjectured that the weighted interval maximum $F(n)$ tends to infinity with $n$. -/
@[category research open, AMS 11]
theorem erdos_1203 :
    Tendsto F atTop atTop := by
  sorry

/-- The formulation on erdosproblems.com asks to prove that the supremum of the weighted
endpoint counts tends to infinity with $n$. -/
@[category research open, AMS 11]
theorem erdos_1203.variants.endpoint : Tendsto endpointF atTop atTop := by
  sorry

/-- For every $\varepsilon>0$, the weighted endpoint supremum is eventually at least
$1-\varepsilon$. -/
@[category research solved, AMS 11]
theorem erdos_1203.variants.lower_bound :
    ∀ ε > 0, ∀ᶠ n in atTop, endpointF n ≥ 1 - ε := by
  sorry

@[category API, AMS 11]
theorem omega_le_intervalMax (n : ℕ) {i t : ℕ} (hi : 1 ≤ i) (hit : i ≤ t) :
    ω (n + i) ≤ intervalMax n t :=
  Finset.le_sup (f := fun j ↦ ω (n + j)) (Finset.mem_Icc.mpr ⟨hi, hit⟩)

/-- Among all intervals of length $t$, the first interval $[1,t]$ minimizes $f(n,t)$.
Every interval of length $t$ contains a multiple of each $m$ with $1\le m\le t$. -/
@[category textbook, AMS 11]
theorem intervalMax_zero_le (n t : ℕ) : intervalMax 0 t ≤ intervalMax n t := by
  apply Finset.sup_le
  intro m hm
  obtain ⟨hm₀, hmt⟩ := Finset.mem_Icc.mp hm
  let i := m - n % m
  have hrem := Nat.mod_lt n hm₀
  have hi : 0 < i := Nat.sub_pos_of_lt hrem
  have hd : m ∣ n + i := by
    have heq : n + i = n - n % m + m := by
      dsimp [i]
      have := Nat.mod_le n m
      omega
    rw [heq]
    exact dvd_add (Nat.dvd_sub_mod _) (dvd_refl m)
  simp only [zero_add]
  calc
    ω m ≤ ω (n + i) := by
      simp only [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
      exact Finset.card_le_card (Nat.primeFactors_mono hd (by omega))
    _ ≤ intervalMax n t := omega_le_intervalMax n hi ((Nat.sub_le ..).trans hmt)

/-- Every interval of length at least the product of the primes up to $x$ contains an
integer with at least $\pi(x)$ distinct prime factors. -/
@[category textbook, AMS 11]
theorem primeCounting_le_intervalMax (n t x : ℕ) (hx : primorial x ≤ t) :
    Nat.primeCounting x ≤ intervalMax n t := by
  have h := omega_le_intervalMax 0 (primorial_pos x) hx
  simpa only [zero_add, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
    primeFactors_primorial, Nat.primesLE_card_eq_primeCounting] using
    h.trans (intervalMax_zero_le n t)

/-- For $T\ge e^e$, bounding all weighted interval maxima with $t\ge T$ is equivalent to
bounding the first weighted interval maximum and every later weighted endpoint. -/
@[category API, AMS 11]
theorem intervalMax_tail_le_iff (n T : ℕ) (hT : exp (exp 1) ≤ (T : ℝ)) (C : ℝ) :
    (∀ t ≥ T, (intervalMax n t : ℝ) * logWeight t ≤ C) ↔
      (intervalMax n T : ℝ) * logWeight T ≤ C ∧
        ∀ k ≥ T, (ω (n + k) : ℝ) * logWeight k ≤ C := by
  have hT₀ : 0 < T := by exact_mod_cast (exp_pos (exp 1)).trans_le hT
  have hlog {t : ℕ} (ht : T ≤ t) : exp 1 ≤ log (t : ℝ) :=
    (le_log_iff_exp_le (by exact_mod_cast hT₀.trans_le ht)).2 (hT.trans (by exact_mod_cast ht))
  have hw {t : ℕ} (ht : T ≤ t) : 0 ≤ logWeight t :=
    div_nonneg (log_nonneg ((one_le_exp_iff.mpr zero_le_one).trans (hlog ht)))
      ((exp_pos 1).le.trans (hlog ht))
  have hanti {i t : ℕ} (hi : T ≤ i) (hit : i ≤ t) : logWeight t ≤ logWeight i :=
    log_div_self_antitoneOn (hlog hi) (hlog (hi.trans hit))
      (log_le_log (by exact_mod_cast hT₀.trans_le hi) (by exact_mod_cast hit))
  constructor
  · intro h
    refine ⟨h T le_rfl, fun k hk ↦ ?_⟩
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (omega_le_intervalMax n (hT₀.trans_le hk) le_rfl)) (hw hk)).trans (h k hk)
  · rintro ⟨hfirst, hend⟩ t ht
    obtain ⟨i, hi, hmax⟩ := (Finset.Icc 1 t).exists_mem_eq_sup
      (Finset.nonempty_Icc.mpr (hT₀.trans_le ht)) (fun j ↦ ω (n + j))
    rw [show intervalMax n t = ω (n + i) from hmax]
    obtain ⟨hi₀, hit⟩ := Finset.mem_Icc.mp hi
    rcases le_total i T with hiT | hTi
    · exact (mul_le_mul (Nat.cast_le.mpr (omega_le_intervalMax n hi₀ hiT))
        (hanti le_rfl ht) (hw ht) (by positivity)).trans hfirst
    · exact (mul_le_mul_of_nonneg_left (hanti hTi hit) (by positivity)).trans (hend i hTi)

end Erdos1203
