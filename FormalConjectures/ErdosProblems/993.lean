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
# Erdős Problem 993

*Reference:* [erdosproblems.com/993](https://www.erdosproblems.com/993)

Let `i_k(T)` denote the number of independent sets of size `k` in a tree `T` (so that
`∑_k i_k(T) x^k` is the *independence polynomial* of `T`). Is the sequence `i_0(T), i_1(T), …`
always **unimodal**?

This was conjectured by Alavi, Malde, Schwenk and Erdős [AMSE87]. It remains **open**: it has
been verified by computer for all trees on at most `29` vertices, but no proof is known.

[AMSE87] Alavi, Y., Malde, P. J., Schwenk, A. J. and Erdős, P., _The vertex independence
sequence of a graph is not constrained_, Congr. Numer. **58** (1987), 15–23.
-/

namespace Erdos993

/-- `indepSeq G k` is the number of `k`-element independent sets of `G`, i.e. the `k`-th term
`i_k(G)` of the independence sequence. -/
noncomputable def indepSeq {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)}

/-- A sequence `a : ℕ → ℕ` is *unimodal* if it is nondecreasing up to some index `m` and
nonincreasing thereafter. -/
def UnimodalSeq (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i)

/-- **Erdős Problem 993.** The independence sequence `i_k(T)` of every finite tree `T` is
unimodal. (Conjectured by Alavi, Malde, Schwenk and Erdős [AMSE87]; open.) -/
@[category research open, AMS 5]
theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → UnimodalSeq (indepSeq G) := by
  sorry

/-
## A proven lemma toward the `d_leaf ≤ 1` case: local tie-balance for the equal-arm spider

The remainder of this file establishes a *genuinely new, fully proven* lemma that is a step
toward the conjecture in the "thin tree" regime, following the strategy of the manuscript
[B. Rey, *Erdős problem 993*, https://github.com/BrettRey/erdos-problem-993].

For a tree `T` write `I_T(x) = ∑_k i_k(T) x^k` and let `μ_T(λ) = λ I_T'(λ) / I_T(λ)` be the
mean of the hard-core distribution at fugacity `λ`. A standard reduction expresses unimodality
through the *tie-fugacity inequality* `μ_T(λ_m) ≥ m - 1`, where `m` is the leftmost mode and
`λ_m = i_{m-1}/i_m`. The manuscript verifies this only finitely (`n ≤ 23`) plus asymptotically.

Here we prove the inequality in **closed form, uniformly in `k`**, for the *equal-arm spider*
`S(2^k)` (the tree obtained by attaching `k` paths of length `2` to a common centre), whose
independence sequence is `c_t = 2^t \binom{k}{t} + \binom{k}{t-1}` (`= iseq k t` below).
In fact we prove the stronger *mode-free local tie-balance*: at **any** rising tie
`c_r ≤ c_{r+1}` we have `μ(λ_r) ≥ r`, equivalently `N_r := ∑_t (t - r) c_t λ_r^t / (\dots) ≥ 0`.
See `equal_spider_local_tie_balance`.

This is partial progress only; Erdős Problem 993 itself remains open.
-/

-- The supporting lemmas below are not Erdős problems, so they carry no `category`/`AMS`
-- attribute; silence the corresponding style linters (cf. `ErdosProblems/655.lean`).
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Finset Nat

namespace SpiderLTB

/-- spider coefficient c_t = 2^t C(k,t) + C(k,t-1) (with C(k,-1)=0). -/
def iseq (k t : ℕ) : ℕ := (if t = 0 then 0 else k.choose (t-1)) + 2^t * (k.choose t)

-- Generating-function bridge: Σ_{t<k+2} iseq(k,t) x^t = (1+2x)^k + x(1+x)^k.
-- iseq(k,t) = (if t=0 then 0 else C(k,t-1)) + 2^t C(k,t).
-- Two halves.

-- Part 1:  Σ 2^t C(k,t) x^t = (1+2x)^k
lemma geom1 (k : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (k+2), (2^t * (k.choose t : ℚ)) * x^t = (1 + 2*x)^k := by
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  rw [add_comm (1:ℚ) (2*x), add_pow]
  rw [show (k+1) = k+1 from rfl]  -- no-op anchor
  simp only [mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [one_pow, mul_one, mul_pow]
  ring

-- Part 2:  Σ (if t=0 then 0 else C(k,t-1)) x^t = x (1+x)^k
lemma geom2 (k : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (k+2), ((if t = 0 then (0:ℚ) else (k.choose (t-1) : ℚ))) * x^t
      = x * (1 + x)^k := by
  rw [Finset.sum_range_succ']   -- peel t=0:  Σ_{i<n} f (i+1) + f 0
  have h0 : (if (0:ℕ) = 0 then (0:ℚ) else (k.choose (0-1):ℚ)) * x^0 = 0 := by simp
  rw [h0, add_zero, add_comm (1:ℚ) x, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hif : (if u+1 = 0 then (0:ℚ) else (k.choose (u+1-1):ℚ)) = (k.choose u : ℚ) := by
    rw [if_neg (Nat.succ_ne_zero u), Nat.add_sub_cancel]
  rw [hif]
  ring

-- Combine: full generating function
lemma genfn (k : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (k+2),
      (((if t = 0 then (0:ℚ) else (k.choose (t-1) : ℚ)) + 2^t * (k.choose t : ℚ))) * x^t
      = (1 + 2*x)^k + x * (1 + x)^k := by
  rw [← geom1 k x, ← geom2 k x, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring


-- Weighted gen.fn. Part A:  Σ t·2^t·C(k,t)·x^t = 2 k x (1+2x)^{k-1},  for k = K+1.
-- absorption:  t * C(K+1,t) = (K+1) * C(K,t-1)   (Nat.succ_mul_choose_eq).
lemma wA (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2), ((t:ℚ) * 2^t * (Nat.choose (K+1) t)) * x^t
      = 2 * (K+1) * x * (1 + 2*x)^K := by
  -- peel t=0 (zero), reindex t=u+1
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  -- Σ_{u<K+2} (u+1)·2^{u+1}·C(K+1,u+1)·x^{u+1} = 2(K+1)x(1+2x)^K
  -- absorption: (u+1)·C(K+1,u+1) = (K+1)·C(K,u)
  rw [add_comm (1:ℚ) (2*x), add_pow, Finset.mul_sum]
  -- both sides over range (K+1) ... but LHS over range (K+2); drop top term (C(K+1,K+2)=0)
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro u hu
  -- (u+1)·2^{u+1}·C(K+1,u+1)·x^{u+1}  vs  2(K+1)x·((2x)^u·1^(K-u)·C(K,u))
  have hq : ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ)
          = (Nat.choose (K+1) (u+1) : ℚ) * ((u+1 : ℕ):ℚ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq K u
  have habs : ((u+1 : ℕ) : ℚ) * (Nat.choose (K+1) (u+1) : ℚ)
            = ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ) := by
    linear_combination -hq
  push_cast at habs ⊢
  linear_combination ((2:ℚ)^(u+1) * x^(u+1)) * habs


-- geomC : Σ C(k,t) x^t = (1+x)^k   (base 1+x, mirror of geom1)
lemma geomC (k : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (k+2), ((k.choose t : ℚ)) * x^t = (1 + x)^k := by
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  rw [add_comm (1:ℚ) x, add_pow]
  simp only [zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [one_pow, mul_one]
  ring

-- wC : Σ t·C(K+1,t)·x^t = (K+1) x (1+x)^K   (base 1+x, no 2^t, mirror of wA)
lemma wC (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2), ((t:ℚ) * (Nat.choose (K+1) t)) * x^t
      = (K+1) * x * (1 + x)^K := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [add_comm (1:ℚ) x, add_pow, Finset.mul_sum]
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro u hu
  have hq : ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ)
          = (Nat.choose (K+1) (u+1) : ℚ) * ((u+1 : ℕ):ℚ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq K u
  have habs : ((u+1 : ℕ) : ℚ) * (Nat.choose (K+1) (u+1) : ℚ)
            = ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ) := by
    linear_combination -hq
  push_cast at habs ⊢
  linear_combination (x^(u+1)) * habs

-- partB : Σ t·(if t=0 then 0 else C(K+1,t-1))·x^t = x(1+x)^{K+1} + (K+1)x²(1+x)^K
lemma partB (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2),
        ((t:ℚ) * (if t = 0 then (0:ℚ) else (Nat.choose (K+1) (t-1):ℚ))) * x^t
      = x*(1+x)^(K+1) + (↑(K+1))*x^2*(1+x)^K := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have step : ∀ u ∈ Finset.range (K+1+1),
      ((↑(u+1):ℚ) * (if u+1 = 0 then (0:ℚ) else (Nat.choose (K+1) ((u+1)-1):ℚ))) * x^(u+1)
      = ((u:ℚ) * Nat.choose (K+1) u) * x^u * x + (Nat.choose (K+1) u : ℚ) * x^u * x := by
    intro u _
    rw [if_neg (Nat.succ_ne_zero u), Nat.add_sub_cancel, pow_succ]
    push_cast; ring
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have e1 : ∑ u ∈ Finset.range (K+1+1), ((u:ℚ) * Nat.choose (K+1) u) * x^u
          = ((K:ℚ)+1)*x*(1+x)^K := by
    have h := wC K x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)] at h
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
    exact_mod_cast h
  have e2 : ∑ u ∈ Finset.range (K+1+1), (Nat.choose (K+1) u : ℚ) * x^u
          = (1+x)^(K+1) := by
    have h := geomC (K+1) x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)] at h
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact_mod_cast h
  rw [e1, e2]; push_cast; ring


/-- plain generating function in terms of `iseq`. -/
lemma genfn_iseq (k : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (k+2), (iseq k t : ℚ) * x^t = (1+2*x)^k + x*(1+x)^k := by
  rw [← genfn k x]
  apply Finset.sum_congr rfl
  intro t _
  simp only [iseq]; push_cast; ring

/-- weighted generating function `Σ t·iseq_t·x^t = x·Z'(x)` (combine wA + partB). -/
lemma wgenfn (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2), ((t:ℚ) * iseq (K+1) t) * x^t
    = 2*((K:ℚ)+1)*x*(1+2*x)^K + (x*(1+x)^(K+1) + ((K:ℚ)+1)*x^2*(1+x)^K) := by
  have split : ∀ t ∈ Finset.range (K+1+2),
      ((t:ℚ) * iseq (K+1) t) * x^t
      = ((t:ℚ) * (if t = 0 then (0:ℚ) else (Nat.choose (K+1) (t-1):ℚ))) * x^t
        + ((t:ℚ) * 2^t * (Nat.choose (K+1) t)) * x^t := by
    intro t _
    simp only [iseq]; push_cast; ring
  rw [Finset.sum_congr rfl split, Finset.sum_add_distrib, partB, wA]
  push_cast; ring


-- Ratio lemma R_r :  iseq_r·(k-r+1) = C(k,r)·(2^r(k-r+1)+r)
lemma R_r (k r : ℕ) (hr : r ≤ k) :
    iseq k r * (k - r + 1) = k.choose r * (2^r * (k-r+1) + r) := by
  rcases Nat.eq_zero_or_pos r with h0 | h1
  · subst h0; simp [iseq]
  · have hiseq : iseq k r = k.choose (r-1) + 2^r * k.choose r := by
      simp only [iseq]; rw [if_neg (by omega)]
    have habs : k.choose (r-1) * (k - r + 1) = k.choose r * r := by
      have h := Nat.choose_succ_right_eq k (r-1)
      rw [show r-1+1 = r by omega, show k - (r-1) = k - r + 1 by omega] at h
      omega
    rw [hiseq, add_mul, habs]; ring

-- Ratio lemma R_r1 :  iseq_{r+1}·(r+1) = C(k,r)·(2^{r+1}(k-r)+(r+1))
lemma R_r1 (k r : ℕ) (_hr : r < k) :
    iseq k (r+1) * (r + 1) = k.choose r * (2^(r+1) * (k-r) + (r+1)) := by
  have hiseq : iseq k (r+1) = k.choose r + 2^(r+1) * k.choose (r+1) := by
    simp only [iseq]; rw [if_neg (by omega), show r+1-1 = r by omega]
  have habs : k.choose (r+1) * (r+1) = k.choose r * (k - r) := Nat.choose_succ_right_eq k r
  rw [hiseq, add_mul, mul_assoc, habs]; ring

-- λ = L/M  (cleared):  iseq_r · M = iseq_{r+1} · L
lemma lam_eq (k r : ℕ) (hr : r < k) :
    iseq k r * ((k-r+1) * (2^(r+1)*(k-r) + (r+1)))
      = iseq k (r+1) * ((r+1) * (2^r*(k-r+1) + r)) := by
  have h1 := R_r k r (by omega)
  have h2 := R_r1 k r hr
  calc iseq k r * ((k-r+1) * (2^(r+1)*(k-r) + (r+1)))
      = (iseq k r * (k-r+1)) * (2^(r+1)*(k-r) + (r+1)) := by ring
    _ = (k.choose r * (2^r*(k-r+1)+r)) * (2^(r+1)*(k-r) + (r+1)) := by rw [h1]
    _ = (k.choose r * (2^(r+1)*(k-r) + (r+1))) * (2^r*(k-r+1)+r) := by ring
    _ = (iseq k (r+1) * (r+1)) * (2^r*(k-r+1)+r) := by rw [h2]
    _ = iseq k (r+1) * ((r+1) * (2^r*(k-r+1) + r)) := by ring


-- Step 1 (named): F = X·A + Y·B  (s = S+1, k = r+S+1, exponent r+S)
lemma step1 (r S : ℕ) (x : ℚ) :
    x * (2 * ((r + S + 1 : ℕ) : ℚ) * (1 + 2*x)^(r+S) + (1+x)^(r+S+1)
         + ((r + S + 1 : ℕ) : ℚ) * x * (1+x)^(r+S))
      - (r : ℚ) * ((1 + 2*x)^(r+S+1) + x * (1+x)^(r+S+1))
    = (1 + 2*x)^(r+S) * (2 * ((S + 1 : ℕ) : ℚ) * x - r)
      + x * (1+x)^(r+S) * (1 - r + (((S + 1 : ℕ) : ℚ) + 1) * x) := by
  rw [pow_succ (1 + 2*x) (r+S), pow_succ (1+x) (r+S)]
  push_cast; ring

-- A-numerator identity (ℕ, s = S+1):  2(S+1)·L = r·M + (2q(S+1)(S+2) + r(r+1)S)
-- where L = (r+1)(q(S+2)+r), M = (S+2)(2q(S+1)+r+1).  ⟹ r·M ≤ 2(S+1)·L.
lemma A_num (r S q : ℕ) :
    2*(S+1) * ((r+1)*(q*(S+2)+r)) = r * ((S+2)*(2*q*(S+1)+r+1)) + (2*q*(S+1)*(S+2) + r*(r+1)*S) := by
  ring

-- Cnum certificate (machine-generated). R,S,Q ≥ 0;  r=R, s=S+1, q=Q+1.  H=M-L.
def Mval (R S Q : ℚ) : ℚ := (S+2)*(2*(Q+1)*(S+1)+R+1)
def Lval (R S Q : ℚ) : ℚ := (R+1)*((Q+1)*(S+2)+R)
set_option maxHeartbeats 4000000 in
def Ppoly (R S Q : ℚ) : ℚ := 6*Q^3*R^2*S^3 + 32*Q^3*R^2*S^2 + 56*Q^3*R^2*S + 32*Q^3*R^2 + 4*Q^3*R*S^5 + 36*Q^3*R*S^4 + 133*Q^3*R*S^3 + 252*Q^3*R*S^2 + 244*Q^3*R*S + 96*Q^3*R + 12*Q^3*S^5 + 90*Q^3*S^4 + 269*Q^3*S^3 + 404*Q^3*S^2 + 308*Q^3*S + 96*Q^3 + 2*Q^2*R^4*S^3 + 5*Q^2*R^4*S^2 + 2*Q^2*R^4*S + 2*Q^2*R^3*S^4 + 12*Q^2*R^3*S^3 + 30*Q^2*R^3*S^2 + 46*Q^2*R^3*S + 36*Q^2*R^3 + 18*Q^2*R^2*S^4 + 116*Q^2*R^2*S^3 + 311*Q^2*R^2*S^2 + 412*Q^2*R^2*S + 220*Q^2*R^2 + 12*Q^2*R*S^5 + 130*Q^2*R*S^4 + 532*Q^2*R*S^3 + 1071*Q^2*R*S^2 + 1084*Q^2*R*S + 444*Q^2*R + 36*Q^2*S^5 + 280*Q^2*S^4 + 872*Q^2*S^3 + 1369*Q^2*S^2 + 1092*Q^2*S + 356*Q^2 + 3*Q*R^5*S^2 + 3*Q*R^5*S + 7*Q*R^4*S^3 + 23*Q*R^4*S^2 + 21*Q*R^4*S + 12*Q*R^4 + 4*Q*R^3*S^4 + 40*Q*R^3*S^3 + 120*Q*R^3*S^2 + 175*Q*R^3*S + 120*Q*R^3 + 34*Q*R^2*S^4 + 226*Q*R^2*S^3 + 600*Q*R^2*S^2 + 779*Q*R^2*S + 416*Q*R^2 + 12*Q*R*S^5 + 152*Q*R*S^4 + 676*Q*R*S^3 + 1437*Q*R*S^2 + 1518*Q*R*S + 648*Q*R + 36*Q*S^5 + 290*Q*S^4 + 939*Q*S^3 + 1537*Q*S^2 + 1280*Q*S + 436*Q + R^6*S + 4*R^5*S^2 + 7*R^5*S + R^5 + 5*R^4*S^3 + 23*R^4*S^2 + 30*R^4*S + 17*R^4 + 2*R^3*S^4 + 27*R^3*S^3 + 93*R^3*S^2 + 140*R^3*S + 93*R^3 + 16*R^2*S^4 + 115*R^2*S^3 + 321*R^2*S^2 + 429*R^2*S + 235*R^2 + 4*R*S^5 + 58*R*S^4 + 277*R*S^3 + 619*R*S^2 + 681*R*S + 302*R + 12*S^5 + 100*S^4 + 336*S^3 + 572*S^2 + 496*S + 176
noncomputable def Cnum (R S Q : ℚ) : ℚ :=
  Mval R S Q*(Mval R S Q+Lval R S Q)*(2*(S+1)*Lval R S Q-R*Mval R S Q)
  + Mval R S Q*Lval R S Q*(R+(S+1)-1)*(2*(S+1)*Lval R S Q-R*Mval R S Q)
  + Lval R S Q*(Mval R S Q+Lval R S Q)*((1-R)*Mval R S Q+(S+2)*Lval R S Q)

lemma P_nonneg (a b c : ℕ) : 0 ≤ Ppoly a b c := by unfold Ppoly; positivity

set_option maxHeartbeats 4000000 in
lemma cnum_cert (R S Q : ℚ) :
    Cnum R S Q = (S+2) * ( Ppoly R S Q + R^2*S*Q^2*(S+2) * (Mval R S Q - Lval R S Q) ) := by
  unfold Cnum Mval Lval Ppoly; ring

lemma cnum_nonneg (a b c : ℕ) (hML : Lval a b c ≤ Mval a b c) :
    0 ≤ Cnum a b c := by
  rw [cnum_cert]
  apply mul_nonneg (by positivity)
  exact add_nonneg (P_nonneg a b c) (mul_nonneg (by positivity) (by linarith [hML]))

-- Core inequality: F = X·A + Y·B ≥ 0, given A ≥ 0 and W ≥ 0 (W from Cnum), via Bernoulli.
lemma core_F_nonneg (r S : ℕ) (lam : ℚ) (hlam : 0 < lam)
    (hA : 0 ≤ 2*((S:ℚ)+1)*lam - r)
    (hW : 0 ≤ (1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)))*(2*((S:ℚ)+1)*lam - r)
              + lam*(1 - r + ((S:ℚ)+2)*lam)) :
    0 ≤ lam * (2*((r+S+1:ℕ):ℚ)*(1+2*lam)^(r+S) + (1+lam)^(r+S+1)
               + ((r+S+1:ℕ):ℚ)*lam*(1+lam)^(r+S))
        - (r:ℚ)*((1+2*lam)^(r+S+1) + lam*(1+lam)^(r+S+1)) := by
  rw [step1 r S lam]
  push_cast
  have h1l : (0:ℚ) < 1 + lam := by linarith
  rcases le_total (0:ℚ) (1 - (r:ℚ) + ((S:ℚ)+1+1)*lam) with hB | hB
  · -- B ≥ 0
    have hXA : 0 ≤ (1+2*lam)^(r+S) * (2*((S:ℚ)+1)*lam - r) :=
      mul_nonneg (by positivity) hA
    have hYB : 0 ≤ lam*(1+lam)^(r+S) * (1 - r + ((S:ℚ)+1+1)*lam) :=
      mul_nonneg (by positivity) hB
    nlinarith [hXA, hYB]
  · -- B < 0 : Bernoulli
    have hber : 1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)) ≤ (1 + lam/(1+lam))^(r+S) :=
      one_add_mul_le_pow (by linarith [div_nonneg hlam.le h1l.le]) (r+S)
    have hXeq : (1+2*lam)^(r+S) = (1+lam)^(r+S) * (1+lam/(1+lam))^(r+S) := by
      rw [← mul_pow]; congr 1; field_simp; ring
    have hXlb : (1+lam)^(r+S) * (1+((r+S:ℕ):ℚ)*(lam/(1+lam))) ≤ (1+2*lam)^(r+S) := by
      rw [hXeq]; exact mul_le_mul_of_nonneg_left hber (by positivity)
    have hXA : (1+lam)^(r+S) * (1+((r+S:ℕ):ℚ)*(lam/(1+lam))) * (2*((S:ℚ)+1)*lam - r)
             ≤ (1+2*lam)^(r+S) * (2*((S:ℚ)+1)*lam - r) :=
      mul_le_mul_of_nonneg_right hXlb hA
    have hWid : (1+lam)^(r+S) * (1+((r+S:ℕ):ℚ)*(lam/(1+lam))) * (2*((S:ℚ)+1)*lam - r)
                + lam*(1+lam)^(r+S) * (1 - r + ((S:ℚ)+1+1)*lam)
              = (1+lam)^(r+S) * ((1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)))*(2*((S:ℚ)+1)*lam - r)
                  + lam*(1 - r + ((S:ℚ)+2)*lam)) := by
      have : ((S:ℚ)+1+1) = ((S:ℚ)+2) := by ring
      rw [this]; ring
    have hfin : 0 ≤ (1+lam)^(r+S) * ((1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)))*(2*((S:ℚ)+1)*lam - r)
                  + lam*(1 - r + ((S:ℚ)+2)*lam)) :=
      mul_nonneg (by positivity) hW
    linarith [hXA, hWid, hfin]


lemma iseq_pos (k t : ℕ) (ht : t ≤ k) : 0 < iseq k t := by
  simp only [iseq]
  have h1 : 0 < k.choose t := Nat.choose_pos ht
  have : 0 < 2^t * k.choose t := by positivity
  omega

-- hA over ℚ (with k = r+s, s ≥ 1):  r·iseq_{r+s,r+1} ≤ 2s·iseq_{r+s,r}.
lemma hA_Q (r s : ℕ) (hs : 1 ≤ s) :
    (r:ℚ) * iseq (r+s) (r+1) ≤ 2*(s:ℚ) * iseq (r+s) r := by
  have hr : r < r+s := by omega
  have hlamQ : (iseq (r+s) r:ℚ) * ((s+1)*(2^(r+1)*s+(r+1)))
             = (iseq (r+s) (r+1):ℚ) * ((r+1)*(2^r*(s+1)+r)) := by
    have h := lam_eq (r+s) r hr
    simp only [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  obtain ⟨S, rfl⟩ : ∃ S, s = S+1 := ⟨s-1, by omega⟩
  have hAQ : 2*((S:ℚ)+1)*((r+1)*(2^r*((S+1)+1)+r))
           = (r:ℚ)*(((S+1)+1)*(2^(r+1)*(S+1)+(r+1)))
             + (2^(r+1)*((S:ℚ)+1)*((S+1)+1) + r*(r+1)*(S:ℚ)) := by
    have h := A_num r S (2^r)
    have hcast : ((2*(S+1) * ((r+1)*(2^r*(S+2)+r)) : ℕ):ℚ)
               = ((r*((S+2)*(2*2^r*(S+1)+r+1)) + (2*2^r*(S+1)*(S+2)+r*(r+1)*S) : ℕ):ℚ) := by exact_mod_cast h
    push_cast [show (2:ℚ)*2^r = 2^(r+1) by rw [pow_succ]; ring] at hcast
    linarith [hcast]
  have hcr1 : (0:ℚ) < iseq (r+(S+1)) (r+1) := by exact_mod_cast iseq_pos (r+(S+1)) (r+1) (by omega)
  have hM : (0:ℚ) < (((S:ℚ)+1+1)*(2^(r+1)*((S:ℚ)+1)+((r:ℚ)+1))) := by positivity
  have hN : (0:ℚ) ≤ (2^(r+1)*((S:ℚ)+1)*((S:ℚ)+1+1) + r*(r+1)*(S:ℚ)) := by positivity
  push_cast at hlamQ hAQ ⊢
  have hclear : (2*((S:ℚ)+1)*(iseq (r+(S+1)) r) - r*(iseq (r+(S+1)) (r+1)))
                * (((S:ℚ)+1+1)*(2^(r+1)*((S:ℚ)+1)+((r:ℚ)+1)))
              = (iseq (r+(S+1)) (r+1)) * (2^(r+1)*((S:ℚ)+1)*((S:ℚ)+1+1) + r*(r+1)*(S:ℚ)) := by
    linear_combination (2*((S:ℚ)+1))*hlamQ + (iseq (r+(S+1)) (r+1) : ℚ)*hAQ
  nlinarith [hclear, mul_nonneg hcr1.le hN, hM]


set_option maxHeartbeats 4000000 in
lemma hW_Q (a b c : ℕ) (hrise : Lval (a:ℚ) (b:ℚ) (c:ℚ) ≤ Mval (a:ℚ) (b:ℚ) (c:ℚ)) :
    0 ≤ (1 + ((a+b:ℕ):ℚ)*((Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
              /(1+Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))))
          * (2*((b:ℚ)+1)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - a)
        + (Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
          * (1 - a + ((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))) := by
  have hMpos : 0 < Mval (a:ℚ) (b:ℚ) (c:ℚ) := by unfold Mval; positivity
  have hLnn : 0 ≤ Lval (a:ℚ) (b:ℚ) (c:ℚ) := by unfold Lval; positivity
  have hMne : Mval (a:ℚ) (b:ℚ) (c:ℚ) ≠ 0 := hMpos.ne'
  have h1Lne : (1 + Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) ≠ 0 := by
    have : (1:ℚ) + Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)
         = (Mval (a:ℚ) (b:ℚ) (c:ℚ) + Lval (a:ℚ) (b:ℚ) (c:ℚ))/Mval (a:ℚ) (b:ℚ) (c:ℚ) := by
      field_simp
    rw [this]; positivity
  have hCnum : 0 ≤ Cnum (a:ℚ) (b:ℚ) (c:ℚ) := cnum_nonneg a b c hrise
  have hden : 0 < Mval (a:ℚ) (b:ℚ) (c:ℚ)^2*(Mval (a:ℚ) (b:ℚ) (c:ℚ)+Lval (a:ℚ) (b:ℚ) (c:ℚ)) := by positivity
  have key : ((1 + ((a+b:ℕ):ℚ)*((Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
                /(1+Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))))
            * (2*((b:ℚ)+1)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - a)
          + (Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
            * (1 - a + ((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))))
          * (Mval (a:ℚ) (b:ℚ) (c:ℚ)^2*(Mval (a:ℚ) (b:ℚ) (c:ℚ)+Lval (a:ℚ) (b:ℚ) (c:ℚ)))
          = Cnum (a:ℚ) (b:ℚ) (c:ℚ) := by
    push_cast
    field_simp
    unfold Cnum Mval Lval
    ring
  nlinarith [key, hCnum, hden]

-- F connection: Σ (t-r)·iseq_t·x^t = core_F closed form (via wgenfn + genfn_iseq).
lemma F_eq (r S : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range ((r+S+1)+2), (((t:ℚ) - r) * iseq (r+S+1) t) * x^t
    = x * (2*((r+S+1:ℕ):ℚ)*(1+2*x)^(r+S) + (1+x)^(r+S+1) + ((r+S+1:ℕ):ℚ)*x*(1+x)^(r+S))
        - (r:ℚ)*((1+2*x)^(r+S+1) + x*(1+x)^(r+S+1)) := by
  have e : ∀ t ∈ Finset.range ((r+S+1)+2),
      (((t:ℚ) - r) * iseq (r+S+1) t) * x^t
      = ((t:ℚ) * iseq (r+S+1) t)*x^t - (r:ℚ)*((iseq (r+S+1) t : ℚ)*x^t) := by
    intro t _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [wgenfn (r+S) x, genfn_iseq (r+S+1) x]
  push_cast; ring


-- subtraction-free ratio at k = r+S+1 (so the final theorem avoids (r+S+1)-r matching)
lemma lam_eq_S (r S : ℕ) :
    iseq (r+S+1) r * ((S+2)*(2^(r+1)*(S+1)+(r+1)))
      = iseq (r+S+1) (r+1) * ((r+1)*(2^r*(S+2)+r)) := by
  have h := lam_eq (r+S+1) r (by omega)
  rw [show (r+S+1)-r = S+1 by omega, show S+1+1 = S+2 by omega] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **Lemma M (local tie-balance) for the equal-arm spider S(2^k)**, toward Erdős #993.
For r < k with the rising tie iseq_r ≤ iseq_{r+1}, N_r = Σ_t (t-r)·iseq_t·iseq_r^t·iseq_{r+1}^{k+1-t} ≥ 0. -/
theorem equal_spider_local_tie_balance (k r : ℕ) (hr : r < k)
    (hrise : iseq k r ≤ iseq k (r+1)) :
    0 ≤ ∑ t ∈ Finset.range (k+2),
        (((t:ℚ) - r) * (iseq k t) * ((iseq k r : ℚ))^t * ((iseq k (r+1) : ℚ))^(k+1-t)) := by
  obtain ⟨S, rfl⟩ : ∃ S, k = r + S + 1 := ⟨k - r - 1, by omega⟩
  set cr : ℚ := (iseq (r+S+1) r : ℚ) with hcr
  set cr1 : ℚ := (iseq (r+S+1) (r+1) : ℚ) with hcr1
  have hcr1pos : 0 < cr1 := by rw [hcr1]; exact_mod_cast iseq_pos (r+S+1) (r+1) (by omega)
  have hcr1ne : cr1 ≠ 0 := hcr1pos.ne'
  have hfact : ∑ t ∈ Finset.range ((r+S+1)+2),
        (((t:ℚ) - r) * (iseq (r+S+1) t) * cr^t * cr1^((r+S+1)+1-t))
      = cr1^((r+S+1)+1) * ∑ t ∈ Finset.range ((r+S+1)+2),
          (((t:ℚ) - r) * (iseq (r+S+1) t)) * (cr/cr1)^t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have htle : t ≤ (r+S+1)+1 := by simp only [Finset.mem_range] at ht; omega
    have hpow : cr^t * cr1^((r+S+1)+1-t) = cr1^((r+S+1)+1) * (cr/cr1)^t := by
      rw [pow_sub₀ _ hcr1ne htle, div_pow]; field_simp
    calc ((t:ℚ) - r) * (iseq (r+S+1) t) * cr^t * cr1^((r+S+1)+1-t)
        = ((t:ℚ) - r) * (iseq (r+S+1) t) * (cr^t * cr1^((r+S+1)+1-t)) := by ring
      _ = ((t:ℚ) - r) * (iseq (r+S+1) t) * (cr1^((r+S+1)+1) * (cr/cr1)^t) := by rw [hpow]
      _ = cr1^((r+S+1)+1) * (((t:ℚ) - r) * (iseq (r+S+1) t) * (cr/cr1)^t) := by ring
  rw [hfact, F_eq r S (cr/cr1)]
  apply mul_nonneg (by positivity)
  -- λ = cr/cr1 = Lval/Mval, plus the rise L ≤ M, plus A ≥ 0
  have hq : ((2^r-1:ℕ):ℚ) + 1 = 2^r := by
    rw [Nat.cast_sub (Nat.one_le_pow r 2 (by norm_num))]; push_cast; ring
  have hLval : Lval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) = ((r+1)*(2^r*(S+2)+r) : ℕ) := by
    unfold Lval; rw [hq]; push_cast; ring
  have hMval : Mval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) = ((S+2)*(2^(r+1)*(S+1)+(r+1)) : ℕ) := by
    unfold Mval; rw [hq]; push_cast [show (2:ℚ)*2^r = 2^(r+1) by rw [pow_succ]; ring]; ring
  have hMvalpos : 0 < Mval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) := by rw [hMval]; positivity
  have heq : cr * Mval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) = cr1 * Lval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) := by
    rw [hMval, hLval, hcr, hcr1, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_inj]
    exact lam_eq_S r S
  have hlamLM : cr/cr1 = Lval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) / Mval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) := by
    rw [div_eq_div_iff hcr1ne hMvalpos.ne']; linear_combination heq
  have hcrle : cr ≤ cr1 := by rw [hcr, hcr1]; exact_mod_cast hrise
  have hLMrise : Lval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) ≤ Mval (r:ℚ) (S:ℚ) ((2^r-1:ℕ):ℚ) := by
    nlinarith [heq, mul_le_mul_of_nonneg_right hcrle hMvalpos.le, hcr1pos]
  have hAlam : 0 ≤ 2*((S:ℚ)+1)*(cr/cr1) - r := by
    have hAq := hA_Q r (S+1) (by omega)
    rw [show r+(S+1) = r+S+1 from rfl] at hAq
    rw [sub_nonneg, ← mul_div_assoc, le_div_iff₀ hcr1pos]
    push_cast at hAq ⊢
    rw [hcr, hcr1]; nlinarith [hAq]
  have hcrpos : 0 < cr := by rw [hcr]; exact_mod_cast iseq_pos (r+S+1) r (by omega)
  have hlampos : 0 < cr/cr1 := div_pos hcrpos hcr1pos
  rw [hlamLM]
  exact core_F_nonneg r S _ (by rw [← hlamLM]; exact hlampos) (by rw [← hlamLM]; exact hAlam)
    (hW_Q r S (2^r-1) hLMrise)
end SpiderLTB


/-
## A second proven lemma: the one-leaf mixed spider `S(2^a,1)`

The same mode-free local tie-balance, now for the spider with `a` length-2 arms plus one
direct leaf, `c_t = 2^t C(a,t) + (2^{t-1}+1) C(a,t-1)`.  Together with the equal-arm case
above this covers both single-hub extremals of the `d_leaf ≤ 1` regime; here the inequality
is even *unconditional* (no rising-tie hypothesis).  See `mixed_spider_one_leaf_local_tie_balance`.
-/

namespace MixedOneLeaf

/-- One-leaf mixed spider S(2^a,1) coefficient c_t = 2^t C(a,t) + (2^{t-1}+1) C(a,t-1)
(with C(a,-1)=0).  This is [x^t] of  (1+2x)^a(1+x) + x(1+x)^a. -/
def mc (a t : ℕ) : ℕ := 2^t * (a.choose t) + (if t = 0 then 0 else (2^(t-1) + 1) * (a.choose (t-1)))

-- Part 1:  Σ 2^t C(a,t) x^t = (1+2x)^a
lemma geom1 (a : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (a+2), (2^t * (a.choose t : ℚ)) * x^t = (1 + 2*x)^a := by
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  rw [add_comm (1:ℚ) (2*x), add_pow]
  simp only [mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [one_pow, mul_one, mul_pow]
  ring

-- mirror with base (1+x):  Σ C(a,t) x^t = (1+x)^a
lemma geomC (a : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (a+2), ((a.choose t : ℚ)) * x^t = (1 + x)^a := by
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  rw [add_comm (1:ℚ) x, add_pow]
  simp only [zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [one_pow, mul_one]
  ring

-- Part 2:  Σ (if t=0 then 0 else (2^{t-1}+1) C(a,t-1)) x^t = x(1+2x)^a + x(1+x)^a
lemma geom2m (a : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (a+2),
        ((if t = 0 then (0:ℚ) else (((2^(t-1) + 1) * a.choose (t-1) : ℕ) : ℚ))) * x^t
      = x*(1+2*x)^a + x*(1+x)^a := by
  rw [Finset.sum_range_succ']
  have h0 : (if (0:ℕ) = 0 then (0:ℚ) else (((2^(0-1) + 1) * a.choose (0-1) : ℕ):ℚ)) * x^0 = 0 := by
    simp
  rw [h0, add_zero]
  -- now Σ_{u<a+1} (2^u+1)·C(a,u)·x^{u+1}
  have step : ∀ u ∈ Finset.range (a+1),
      ((if u+1 = 0 then (0:ℚ) else (((2^((u+1)-1) + 1) * a.choose ((u+1)-1) : ℕ):ℚ))) * x^(u+1)
      = (2^u * (a.choose u : ℚ)) * x^u * x + ((a.choose u : ℚ)) * x^u * x := by
    intro u _
    rw [if_neg (Nat.succ_ne_zero u), Nat.add_sub_cancel, pow_succ]
    push_cast; ring
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  -- the two sums over range (a+1) equal (1+2x)^a and (1+x)^a
  have e1 : ∑ u ∈ Finset.range (a+1), (2^u * (a.choose u : ℚ)) * x^u = (1+2*x)^a := by
    have h := geom1 a x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show a < a+1 by omega)] at h
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
    exact h
  have e2 : ∑ u ∈ Finset.range (a+1), ((a.choose u : ℚ)) * x^u = (1+x)^a := by
    have h := geomC a x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show a < a+1 by omega)] at h
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact h
  rw [e1, e2]; ring

/-- plain generating function  Σ mc(a,t) x^t = (1+2x)^a(1+x) + x(1+x)^a. -/
lemma genfn_mc (a : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (a+2), (mc a t : ℚ) * x^t = (1+2*x)^a*(1+x) + x*(1+x)^a := by
  have split : ∀ t ∈ Finset.range (a+2),
      (mc a t : ℚ) * x^t
      = (2^t * (a.choose t : ℚ)) * x^t
        + ((if t = 0 then (0:ℚ) else (((2^(t-1) + 1) * a.choose (t-1) : ℕ):ℚ))) * x^t := by
    intro t _
    simp only [mc]
    split_ifs with h
    · push_cast; ring
    · push_cast; ring
  rw [Finset.sum_congr rfl split, Finset.sum_add_distrib, geom1, geom2m]
  ring

-- weighted: Σ t·2^t C(a,t) x^t = 2a x (1+2x)^{a-1}  (a = K+1)
lemma wA (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2), ((t:ℚ) * 2^t * (Nat.choose (K+1) t)) * x^t
      = 2 * (K+1) * x * (1 + 2*x)^K := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [add_comm (1:ℚ) (2*x), add_pow, Finset.mul_sum]
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro u _
  have hq : ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ)
          = (Nat.choose (K+1) (u+1) : ℚ) * ((u+1 : ℕ):ℚ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq K u
  have habs : ((u+1 : ℕ) : ℚ) * (Nat.choose (K+1) (u+1) : ℚ)
            = ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ) := by
    linear_combination -hq
  push_cast at habs ⊢
  linear_combination ((2:ℚ)^(u+1) * x^(u+1)) * habs

-- weighted: Σ t·C(a,t) x^t = a x (1+x)^{a-1}  (a = K+1)
lemma wC (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2), ((t:ℚ) * (Nat.choose (K+1) t)) * x^t
      = (K+1) * x * (1 + x)^K := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [add_comm (1:ℚ) x, add_pow, Finset.mul_sum]
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro u _
  have hq : ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ)
          = (Nat.choose (K+1) (u+1) : ℚ) * ((u+1 : ℕ):ℚ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq K u
  have habs : ((u+1 : ℕ) : ℚ) * (Nat.choose (K+1) (u+1) : ℚ)
            = ((K+1 : ℕ):ℚ) * (Nat.choose K u : ℚ) := by
    linear_combination -hq
  push_cast at habs ⊢
  linear_combination (x^(u+1)) * habs

-- weighted part with 2^{t-1}:  Σ t·(if t=0 then 0 else 2^{t-1} C(a,t-1)) x^t
--   = 2a x^2 (1+2x)^{a-1} + x (1+2x)^a   (a = K+1)
lemma w2C (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2),
        ((t:ℚ) * (if t = 0 then (0:ℚ) else (2^(t-1) * Nat.choose (K+1) (t-1):ℚ))) * x^t
      = 2*((K:ℚ)+1)*x^2*(1+2*x)^K + x*(1+2*x)^(K+1) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have step : ∀ u ∈ Finset.range (K+1+1),
      ((↑(u+1):ℚ) * (if u+1 = 0 then (0:ℚ) else (2^((u+1)-1)*Nat.choose (K+1) ((u+1)-1):ℚ))) * x^(u+1)
      = ((u:ℚ) * 2^u * Nat.choose (K+1) u) * x^u * x + (2^u * Nat.choose (K+1) u : ℚ) * x^u * x := by
    intro u _
    rw [if_neg (Nat.succ_ne_zero u), Nat.add_sub_cancel, pow_succ]
    push_cast; ring
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have e1 : ∑ u ∈ Finset.range (K+1+1), ((u:ℚ) * 2^u * Nat.choose (K+1) u) * x^u
          = 2*((K:ℚ)+1)*x*(1+2*x)^K := by
    have h := wA K x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)] at h
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
    linarith [h]
  have e2 : ∑ u ∈ Finset.range (K+1+1), (2^u * Nat.choose (K+1) u : ℚ) * x^u
          = (1+2*x)^(K+1) := by
    have h := geom1 (K+1) x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)] at h
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
    exact_mod_cast h
  rw [e1, e2]; ring

-- weighted part with plain C:  Σ t·(if t=0 then 0 else C(a,t-1)) x^t
--   = x (1+x)^a + a x^2 (1+x)^{a-1}   (a = K+1)
lemma wCm (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2),
        ((t:ℚ) * (if t = 0 then (0:ℚ) else (Nat.choose (K+1) (t-1):ℚ))) * x^t
      = x*(1+x)^(K+1) + ((K:ℚ)+1)*x^2*(1+x)^K := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have step : ∀ u ∈ Finset.range (K+1+1),
      ((↑(u+1):ℚ) * (if u+1 = 0 then (0:ℚ) else (Nat.choose (K+1) ((u+1)-1):ℚ))) * x^(u+1)
      = ((u:ℚ) * Nat.choose (K+1) u) * x^u * x + (Nat.choose (K+1) u : ℚ) * x^u * x := by
    intro u _
    rw [if_neg (Nat.succ_ne_zero u), Nat.add_sub_cancel, pow_succ]
    push_cast; ring
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have e1 : ∑ u ∈ Finset.range (K+1+1), ((u:ℚ) * Nat.choose (K+1) u) * x^u
          = ((K:ℚ)+1)*x*(1+x)^K := by
    have h := wC K x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)] at h
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
    linarith [h]
  have e2 : ∑ u ∈ Finset.range (K+1+1), (Nat.choose (K+1) u : ℚ) * x^u
          = (1+x)^(K+1) := by
    have h := geomC (K+1) x
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show K+1 < K+1+1 by omega)] at h
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact_mod_cast h
  rw [e1, e2]; ring

/-- weighted generating function  Σ t·mc(K+1,t)·x^t = x·Z'(x). -/
lemma wgenfn_mc (K : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (K+1+2), ((t:ℚ) * mc (K+1) t) * x^t
    = 2*((K:ℚ)+1)*x*(1+2*x)^K
      + (2*((K:ℚ)+1)*x^2*(1+2*x)^K + x*(1+2*x)^(K+1))
      + (x*(1+x)^(K+1) + ((K:ℚ)+1)*x^2*(1+x)^K) := by
  have split : ∀ t ∈ Finset.range (K+1+2),
      ((t:ℚ) * mc (K+1) t) * x^t
      = ((t:ℚ) * 2^t * (Nat.choose (K+1) t)) * x^t
        + ((t:ℚ) * (if t = 0 then (0:ℚ) else (2^(t-1) * Nat.choose (K+1) (t-1):ℚ))) * x^t
        + ((t:ℚ) * (if t = 0 then (0:ℚ) else (Nat.choose (K+1) (t-1):ℚ))) * x^t := by
    intro t _
    simp only [mc]
    split_ifs with h
    · push_cast; ring
    · push_cast; ring
  rw [Finset.sum_congr rfl split, Finset.sum_add_distrib, Finset.sum_add_distrib, wA, w2C, wCm]

/-- F = x·Z'(x) − r·Z(x) = (1+2x)^{a-1}·A + x(1+x)^{a-1}·B, with a = r+S+1, s = S+1,
A = 2(s+1)x²+(2s+1−r)x−r, B = (1−r)+(s+1)x.  (Step-1, verified `derive_oneleaf.py` S1.) -/
lemma F_eq (r S : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range ((r+S+1)+2), (((t:ℚ) - r) * mc (r+S+1) t) * x^t
    = (1+2*x)^(r+S) * (2*((S:ℚ)+2)*x^2 + (2*(S:ℚ)+3-r)*x - r)
      + x*(1+x)^(r+S) * (1 - r + ((S:ℚ)+2)*x) := by
  have e : ∀ t ∈ Finset.range ((r+S+1)+2),
      (((t:ℚ) - r) * mc (r+S+1) t) * x^t
      = ((t:ℚ) * mc (r+S+1) t)*x^t - (r:ℚ)*((mc (r+S+1) t : ℚ)*x^t) := by
    intro t _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [wgenfn_mc (r+S) x, genfn_mc (r+S+1) x]
  rw [pow_succ (1+2*x) (r+S), pow_succ (1+x) (r+S)]
  push_cast; ring

-- mc positive (t ≤ a)
lemma mc_pos (a t : ℕ) (ht : t ≤ a) : 0 < mc a t := by
  simp only [mc]
  have h1 : 0 < 2^t * a.choose t := Nat.mul_pos (by positivity) (Nat.choose_pos ht)
  split_ifs with h
  · omega
  · have : 0 ≤ (2^(t-1)+1) * a.choose (t-1) := Nat.zero_le _
    omega

-- absorption (ℚ), r=R+1, a=R+1+s:  (s+1)·C(a,R) = (R+1)·C(a,R+1)
lemma absR (R s : ℕ) :
    ((s+1 : ℕ):ℚ) * ((R+1+s).choose R : ℚ) = ((R+1 : ℕ):ℚ) * ((R+1+s).choose (R+1) : ℚ) := by
  have h := Nat.choose_succ_right_eq (R+1+s) R
  -- C(a,R+1)·(R+1) = C(a,R)·(a-R) = C(a,R)·(s+1)
  rw [show (R+1+s) - R = s+1 by omega] at h
  have : ((R+1+s).choose (R+1) * (R+1) : ℕ) = ((R+1+s).choose R * (s+1) : ℕ) := h
  have hq : (((R+1+s).choose (R+1) * (R+1) : ℕ):ℚ) = (((R+1+s).choose R * (s+1) : ℕ):ℚ) := by
    exact_mod_cast this
  push_cast at hq ⊢; linear_combination -hq

-- absorption (ℚ):  s·C(a,R+1) = (R+2)·C(a,R+2)
lemma absR1 (R s : ℕ) :
    ((s : ℕ):ℚ) * ((R+1+s).choose (R+1) : ℚ) = ((R+2 : ℕ):ℚ) * ((R+1+s).choose (R+2) : ℚ) := by
  have h := Nat.choose_succ_right_eq (R+1+s) (R+1)
  rw [show (R+1+s) - (R+1) = s by omega, show (R+1)+1 = R+2 by omega] at h
  have : ((R+1+s).choose (R+2) * (R+2) : ℕ) = ((R+1+s).choose (R+1) * s : ℕ) := h
  have hq : (((R+1+s).choose (R+2) * (R+2) : ℕ):ℚ) = (((R+1+s).choose (R+1) * s : ℕ):ℚ) := by
    exact_mod_cast this
  push_cast at hq ⊢; linear_combination -hq

-- mc expansion (ℚ) at r=R+1
lemma mc_r_eq (R s : ℕ) :
    (mc (R+1+s) (R+1) : ℚ)
      = 2^(R+1) * ((R+1+s).choose (R+1) : ℚ) + (2^R+1) * ((R+1+s).choose R : ℚ) := by
  simp only [mc]; rw [if_neg (by omega), show (R+1)-1 = R by omega]; push_cast; ring

lemma mc_r1_eq (R s : ℕ) :
    (mc (R+1+s) (R+2) : ℚ)
      = 2^(R+2) * ((R+1+s).choose (R+2) : ℚ) + (2^(R+1)+1) * ((R+1+s).choose (R+1) : ℚ) := by
  simp only [mc]
  rw [if_neg (by omega), show (R+2)-1 = R+1 by omega]
  push_cast; ring

-- tie half-identities (q = 2^(R+1) = 2^r):
-- 2·mc_r·(s+1) = C(a,R+1)·BR,  BR = 2q(s+1)+(q+2)(R+1)
lemma tieL (R s : ℕ) :
    2 * (mc (R+1+s) (R+1) : ℚ) * ((s:ℚ)+1)
      = ((R+1+s).choose (R+1) : ℚ) * (2*2^(R+1)*((s:ℚ)+1)+(2^(R+1)+2)*((R:ℚ)+1)) := by
  rw [mc_r_eq]
  have hA := absR R s
  have hp : (2:ℚ)^(R+1) = 2*2^R := by rw [pow_succ]; ring
  rw [hp]
  push_cast at hA ⊢
  linear_combination (2*(2:ℚ)^R+2) * hA

-- mc_{r+1}·(R+2) = C(a,R+1)·BR1,  BR1 = 2q·s+(q+1)(R+2)
lemma tieR (R s : ℕ) :
    (mc (R+1+s) (R+2) : ℚ) * ((R:ℚ)+2)
      = ((R+1+s).choose (R+1) : ℚ) * (2*2^(R+1)*(s:ℚ)+(2^(R+1)+1)*((R:ℚ)+2)) := by
  rw [mc_r1_eq]
  have hA := absR1 R s
  have hp2 : (2:ℚ)^(R+2) = 2*2^(R+1) := by rw [pow_succ]; ring
  rw [hp2]
  push_cast at hA ⊢
  linear_combination (-(2*(2:ℚ)^(R+1))) * hA

-- tie:  mc_r · M = mc_{r+1} · L,  L=(R+2)·BR, M=2(s+1)·BR1
lemma lam_eq (R s : ℕ) :
    (mc (R+1+s) (R+1):ℚ) * (2*((s:ℚ)+1)*(2*2^(R+1)*(s:ℚ)+(2^(R+1)+1)*((R:ℚ)+2)))
      = (mc (R+1+s) (R+2):ℚ) * (((R:ℚ)+2)*(2*2^(R+1)*((s:ℚ)+1)+(2^(R+1)+2)*((R:ℚ)+1))) := by
  have hL := tieL R s
  have hR := tieR R s
  linear_combination (2*2^(R+1)*(s:ℚ)+(2^(R+1)+1)*((R:ℚ)+2)) * hL
    - (2*2^(R+1)*((s:ℚ)+1)+(2^(R+1)+2)*((R:ℚ)+1)) * hR

-- Core inequality: F = X·A + Y·B ≥ 0 given A ≥ 0 and W ≥ 0 (the Bernoulli-reduced C),
-- with A = 2(S+2)λ²+(2S+3−r)λ−r (quadratic), B = 1−r+(S+2)λ.
lemma core_F_nonneg (r S : ℕ) (lam : ℚ) (hlam : 0 < lam)
    (hA : 0 ≤ 2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
    (hW : 0 ≤ (1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)))
                * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
              + lam*(1 - r + ((S:ℚ)+2)*lam)) :
    0 ≤ (1+2*lam)^(r+S) * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
        + lam*(1+lam)^(r+S) * (1 - r + ((S:ℚ)+2)*lam) := by
  have h1l : (0:ℚ) < 1 + lam := by linarith
  rcases le_total (0:ℚ) (1 - (r:ℚ) + ((S:ℚ)+2)*lam) with hB | hB
  · have hXA : 0 ≤ (1+2*lam)^(r+S) * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r) :=
      mul_nonneg (by positivity) hA
    have hYB : 0 ≤ lam*(1+lam)^(r+S) * (1 - r + ((S:ℚ)+2)*lam) :=
      mul_nonneg (by positivity) hB
    linarith [hXA, hYB]
  · have hber : 1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)) ≤ (1 + lam/(1+lam))^(r+S) :=
      one_add_mul_le_pow (by have := div_nonneg hlam.le h1l.le; linarith) (r+S)
    have hXeq : (1+2*lam)^(r+S) = (1+lam)^(r+S) * (1+lam/(1+lam))^(r+S) := by
      rw [← mul_pow]; congr 1; field_simp; ring
    have hXlb : (1+lam)^(r+S) * (1+((r+S:ℕ):ℚ)*(lam/(1+lam))) ≤ (1+2*lam)^(r+S) := by
      rw [hXeq]; exact mul_le_mul_of_nonneg_left hber (by positivity)
    have hXA : (1+lam)^(r+S) * (1+((r+S:ℕ):ℚ)*(lam/(1+lam)))
                 * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
             ≤ (1+2*lam)^(r+S) * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r) :=
      mul_le_mul_of_nonneg_right hXlb hA
    have hWid : (1+lam)^(r+S) * (1+((r+S:ℕ):ℚ)*(lam/(1+lam)))
                  * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
                + lam*(1+lam)^(r+S) * (1 - r + ((S:ℚ)+2)*lam)
              = (1+lam)^(r+S) * ((1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)))
                    * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
                  + lam*(1 - r + ((S:ℚ)+2)*lam)) := by ring
    have hfin : 0 ≤ (1+lam)^(r+S) * ((1 + ((r+S:ℕ):ℚ)*(lam/(1+lam)))
                    * (2*((S:ℚ)+2)*lam^2 + (2*(S:ℚ)+3-r)*lam - r)
                  + lam*(1 - r + ((S:ℚ)+2)*lam)) :=
      mul_nonneg (by positivity) hW
    linarith [hXA, hWid, hfin]

-- Cnum positivity certificate (machine-generated, gen_cnum_mixed.py).  sg = S+1, q ≥ 0.
def Mval (r S q : ℚ) : ℚ := 2*(S+2)*((r+1)*(q+1)+2*q*(S+1))
def Lval (r S q : ℚ) : ℚ := (r+1)*(2*q*(S+2)+r*(q+2))
def Araw (r S q : ℚ) : ℚ :=
  2*(S+2)*(Lval r S q)^2 + (2*S+3-r)*(Lval r S q)*(Mval r S q) - r*(Mval r S q)^2
def Braw (r S q : ℚ) : ℚ := (1-r)*(Mval r S q) + (S+2)*(Lval r S q)
set_option maxHeartbeats 4000000 in
def Ppoly (r S q : ℚ) : ℚ := 2*r^7*q^2 + 8*r^7*q + 8*r^7 + 14*r^6*S*q^2 + 36*r^6*S*q + 16*r^6*S + 1*r^6*q^3 + 34*r^6*q^2 + 84*r^6*q + 40*r^6 + 36*r^5*S^2*q^2 + 52*r^5*S^2*q + 8*r^5*S^2 + 10*r^5*S*q^3 + 186*r^5*S*q^2 + 272*r^5*S*q + 72*r^5*S + 27*r^5*q^3 + 254*r^5*q^2 + 356*r^5*q + 104*r^5 + 40*r^4*S^3*q^2 + 24*r^4*S^3*q + 40*r^4*S^2*q^3 + 372*r^4*S^2*q^2 + 292*r^4*S^2*q + 32*r^4*S^2 + 202*r^4*S*q^3 + 1114*r^4*S*q^2 + 936*r^4*S*q + 152*r^4*S + 251*r^4*q^3 + 1090*r^4*q^2 + 932*r^4*q + 184*r^4 + 16*r^3*S^4*q^2 + 80*r^3*S^3*q^3 + 328*r^3*S^3*q^2 + 104*r^3*S^3*q + 596*r^3*S^2*q^3 + 1780*r^3*S^2*q^2 + 756*r^3*S^2*q + 48*r^3*S^2 + 1462*r^3*S*q^3 + 3822*r^3*S*q^2 + 1872*r^3*S*q + 184*r^3*S + 1177*r^3*q^3 + 2888*r^3*q^2 + 1572*r^3*q + 208*r^3 + 80*r^2*S^4*q^3 + 112*r^2*S^4*q^2 + 840*r^2*S^3*q^3 + 1144*r^2*S^3*q^2 + 152*r^2*S^3*q + 3168*r^2*S^2*q^3 + 4332*r^2*S^2*q^2 + 940*r^2*S^2*q + 32*r^2*S^2 + 5142*r^2*S*q^3 + 7216*r^2*S*q^2 + 2036*r^2*S*q + 120*r^2*S + 3048*r^2*q^3 + 4452*r^2*q^2 + 1528*r^2*q + 128*r^2 + 32*r*S^5*q^3 + 528*r*S^4*q^3 + 176*r*S^4*q^2 + 2912*r*S^3*q^3 + 1464*r*S^3*q^2 + 88*r*S^3*q + 7380*r*S^2*q^3 + 4632*r*S^2*q^2 + 520*r*S^2*q + 8*r*S^2 + 8896*r*S*q^3 + 6576*r*S*q^2 + 1056*r*S*q + 32*r*S + 4144*r*q^3 + 3520*r*q^2 + 736*r*q + 32*r + 96*S^5*q^3 + 896*S^4*q^3 + 80*S^4*q^2 + 3368*S^3*q^3 + 608*S^3*q^2 + 16*S^3*q + 6368*S^2*q^3 + 1744*S^2*q^2 + 96*S^2*q + 6048*S*q^3 + 2240*S*q^2 + 192*S*q + 2304*q^3 + 1088*q^2 + 128*q
noncomputable def Cnum (r S q : ℚ) : ℚ :=
  (Araw r S q)*(Mval r S q+Lval r S q) + (Araw r S q)*(r+S)*(Lval r S q)
  + (Braw r S q)*(Lval r S q)*(Mval r S q+Lval r S q)

lemma P_nonneg (a b c : ℕ) : 0 ≤ Ppoly a b c := by unfold Ppoly; positivity

set_option maxHeartbeats 4000000 in
lemma cnum_cert (r S q : ℚ) : Cnum r S q = (S+2) * Ppoly r S q := by
  unfold Cnum Araw Braw Mval Lval Ppoly; ring

lemma cnum_nonneg (a b c : ℕ) : 0 ≤ Cnum a b c := by
  rw [cnum_cert]
  have hP := P_nonneg a b c
  have : (0:ℚ) ≤ (b:ℚ)+2 := by positivity
  exact mul_nonneg this hP

-- A_pos:  Araw = 2(S+2)·A_pos,  A_pos all-nonneg coeffs.
set_option maxHeartbeats 4000000 in
def Apos (r S q : ℚ) : ℚ := 1*r^4*q + 2*r^4 + 4*r^3*S*q + 2*r^3*S + 1*r^3*q^2 + 11*r^3*q + 6*r^3 + 4*r^2*S^2*q + 6*r^2*S*q^2 + 22*r^2*S*q + 4*r^2*S + 14*r^2*q^2 + 31*r^2*q + 6*r^2 + 12*r*S^2*q^2 + 8*r*S^2*q + 48*r*S*q^2 + 32*r*S*q + 2*r*S + 49*r*q^2 + 33*r*q + 2*r + 8*S^3*q^2 + 44*S^2*q^2 + 4*S^2*q + 82*S*q^2 + 14*S*q + 52*q^2 + 12*q

lemma Apos_nonneg (a b c : ℕ) : 0 ≤ Apos a b c := by unfold Apos; positivity

set_option maxHeartbeats 4000000 in
lemma araw_cert (r S q : ℚ) : Araw r S q = 2*(S+2) * Apos r S q := by
  unfold Araw Apos Mval Lval; ring

lemma araw_nonneg (a b c : ℕ) : 0 ≤ Araw (a:ℚ) (b:ℚ) (c:ℚ) := by
  rw [araw_cert]
  have := Apos_nonneg a b c
  have h2 : (0:ℚ) ≤ 2*((b:ℚ)+2) := by positivity
  exact mul_nonneg h2 this

-- A(λ) ≥ 0 at λ = Lval/Mval
lemma hA_Q (a b c : ℕ) :
    0 ≤ 2*((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))^2
        + (2*(b:ℚ)+3-(a:ℚ))*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - (a:ℚ) := by
  have hMpos : 0 < Mval (a:ℚ) (b:ℚ) (c:ℚ) := by unfold Mval; positivity
  have hAraw := araw_nonneg a b c
  have hkey : (2*((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))^2
        + (2*(b:ℚ)+3-(a:ℚ))*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - (a:ℚ))
        * (Mval (a:ℚ) (b:ℚ) (c:ℚ))^2 = Araw (a:ℚ) (b:ℚ) (c:ℚ) := by
    unfold Araw; field_simp
  have hA_eq : (2*((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))^2
        + (2*(b:ℚ)+3-(a:ℚ))*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - (a:ℚ))
        = Araw (a:ℚ) (b:ℚ) (c:ℚ) / (Mval (a:ℚ) (b:ℚ) (c:ℚ))^2 := by
    rw [eq_div_iff (by positivity)]; exact hkey
  rw [hA_eq]; exact div_nonneg hAraw (by positivity)

-- W ≥ 0 at λ = Lval/Mval  (W·Mval²(Mval+Lval) = Cnum)
set_option maxHeartbeats 4000000 in
lemma hW_Q (a b c : ℕ) :
    0 ≤ (1 + ((a+b:ℕ):ℚ)*((Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
              /(1+Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))))
          * (2*((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))^2
             + (2*(b:ℚ)+3-(a:ℚ))*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - (a:ℚ))
        + (Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
          * (1 - (a:ℚ) + ((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))) := by
  have hMpos : 0 < Mval (a:ℚ) (b:ℚ) (c:ℚ) := by unfold Mval; positivity
  have hLnn : 0 ≤ Lval (a:ℚ) (b:ℚ) (c:ℚ) := by unfold Lval; positivity
  have hMne : Mval (a:ℚ) (b:ℚ) (c:ℚ) ≠ 0 := hMpos.ne'
  have h1Lne : (1 + Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) ≠ 0 := by
    have : (1:ℚ) + Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)
         = (Mval (a:ℚ) (b:ℚ) (c:ℚ) + Lval (a:ℚ) (b:ℚ) (c:ℚ))/Mval (a:ℚ) (b:ℚ) (c:ℚ) := by
      field_simp
    rw [this]; positivity
  have hCnum := cnum_nonneg a b c
  have hden : 0 < (Mval (a:ℚ) (b:ℚ) (c:ℚ))^2*(Mval (a:ℚ) (b:ℚ) (c:ℚ)+Lval (a:ℚ) (b:ℚ) (c:ℚ)) := by
    positivity
  have key : ((1 + ((a+b:ℕ):ℚ)*((Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
              /(1+Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))))
          * (2*((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))^2
             + (2*(b:ℚ)+3-(a:ℚ))*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ)) - (a:ℚ))
        + (Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))
          * (1 - (a:ℚ) + ((b:ℚ)+2)*(Lval (a:ℚ) (b:ℚ) (c:ℚ)/Mval (a:ℚ) (b:ℚ) (c:ℚ))))
        * ((Mval (a:ℚ) (b:ℚ) (c:ℚ))^2*(Mval (a:ℚ) (b:ℚ) (c:ℚ)+Lval (a:ℚ) (b:ℚ) (c:ℚ)))
        = Cnum (a:ℚ) (b:ℚ) (c:ℚ) := by
    push_cast
    field_simp
    unfold Cnum Araw Braw Mval Lval
    ring
  nlinarith [key, hCnum, hden]

set_option maxHeartbeats 4000000 in
/-- **Local tie-balance for the one-leaf mixed spider `S(2^a,1)`** (toward Erdős #993).
For every `r < a`, with `c_t = mc a t = 2^t C(a,t) + (2^{t-1}+1) C(a,t-1)`,
`N_r = ∑_t (t-r) c_t c_r^t c_{r+1}^{a+1-t} ≥ 0` — *unconditionally* (no rising-tie hypothesis). -/
theorem mixed_spider_one_leaf_local_tie_balance (a r : ℕ) (hr : r < a) :
    0 ≤ ∑ t ∈ Finset.range (a+2),
        (((t:ℚ) - r) * (mc a t) * ((mc a r : ℚ))^t * ((mc a (r+1) : ℚ))^(a+1-t)) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- r = 0 : every summand is ≥ 0
    subst hr0
    apply Finset.sum_nonneg
    intro t _
    have e : ((t:ℚ) - ((0:ℕ):ℚ)) = (t:ℚ) := by push_cast; ring
    rw [e]
    positivity
  · obtain ⟨R, rfl⟩ : ∃ R, r = R+1 := ⟨r-1, by omega⟩
    obtain ⟨S, rfl⟩ : ∃ S, a = R+1+S+1 := ⟨a-(R+1)-1, by omega⟩
    set cr : ℚ := (mc (R+1+S+1) (R+1) : ℚ) with hcr
    set cr1 : ℚ := (mc (R+1+S+1) (R+1+1) : ℚ) with hcr1
    have hcr1pos : 0 < cr1 := by rw [hcr1]; exact_mod_cast mc_pos (R+1+S+1) (R+1+1) (by omega)
    have hcr1ne : cr1 ≠ 0 := hcr1pos.ne'
    have hcrpos : 0 < cr := by rw [hcr]; exact_mod_cast mc_pos (R+1+S+1) (R+1) (by omega)
    -- factor: sum = cr1^(a+1) * Σ (t-r)·mc_t·(cr/cr1)^t
    have hfact : ∑ t ∈ Finset.range ((R+1+S+1)+2),
          (((t:ℚ) - ((R+1:ℕ):ℚ)) * (mc (R+1+S+1) t) * cr^t * cr1^((R+1+S+1)+1-t))
        = cr1^((R+1+S+1)+1) * ∑ t ∈ Finset.range ((R+1+S+1)+2),
            (((t:ℚ) - ((R+1:ℕ):ℚ)) * (mc (R+1+S+1) t)) * (cr/cr1)^t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have htle : t ≤ (R+1+S+1)+1 := by simp only [Finset.mem_range] at ht; omega
      have hpow : cr^t * cr1^((R+1+S+1)+1-t) = cr1^((R+1+S+1)+1) * (cr/cr1)^t := by
        rw [pow_sub₀ _ hcr1ne htle, div_pow]; field_simp
      calc ((t:ℚ) - ((R+1:ℕ):ℚ)) * (mc (R+1+S+1) t) * cr^t * cr1^((R+1+S+1)+1-t)
          = ((t:ℚ) - ((R+1:ℕ):ℚ)) * (mc (R+1+S+1) t) * (cr^t * cr1^((R+1+S+1)+1-t)) := by ring
        _ = ((t:ℚ) - ((R+1:ℕ):ℚ)) * (mc (R+1+S+1) t) * (cr1^((R+1+S+1)+1) * (cr/cr1)^t) := by rw [hpow]
        _ = cr1^((R+1+S+1)+1) * (((t:ℚ) - ((R+1:ℕ):ℚ)) * (mc (R+1+S+1) t) * (cr/cr1)^t) := by ring
    rw [hfact, F_eq (R+1) S (cr/cr1)]
    apply mul_nonneg (by positivity)
    -- tie:  cr/cr1 = Lval/Mval  with q = 2^(R+1)
    have hqcast : ((2^(R+1):ℕ):ℚ) = (2:ℚ)^(R+1) := by push_cast; ring
    have hMpos : 0 < Mval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ) := by unfold Mval; positivity
    have heq : cr * Mval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ)
             = cr1 * Lval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ) := by
      have h := lam_eq R (S+1)
      simp only [show R+1+(S+1) = R+1+S+1 from rfl, show R+2 = R+1+1 from rfl] at h
      rw [hcr, hcr1]
      unfold Mval Lval
      rw [hqcast]
      push_cast at h ⊢
      linear_combination h
    have hlamLM : cr/cr1 = Lval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ) / Mval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ) := by
      rw [div_eq_div_iff hcr1ne hMpos.ne']; linear_combination heq
    rw [hlamLM]
    have hlampos : 0 < Lval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ) / Mval ((R+1:ℕ):ℚ) (S:ℚ) ((2^(R+1):ℕ):ℚ) := by
      apply div_pos _ hMpos; unfold Lval; positivity
    exact core_F_nonneg (R+1) S _ hlampos (hA_Q (R+1) S (2^(R+1))) (hW_Q (R+1) S (2^(R+1)))

end MixedOneLeaf

end Erdos993
