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
# Conjectures associated with A063880

A063880 lists numbers $n$ such that $\sigma(n) = 2 \cdot \text{usigma}(n)$, where $\sigma(n)$ is the
sum of all divisors and $\text{usigma}(n)$ is the sum of unitary divisors.

Equivalently, these are numbers whose unitary and non-unitary divisors have equal sum.

The conjectures state that all members satisfy $n \equiv 108 \pmod{216}$, and that all
primitive terms (those whose proper divisors aren't in the sequence) are powerful numbers,
with $108$ being the only primitive term.

*References:*
- [A063880](https://oeis.org/A063880)
-/

@[expose] public section

namespace OeisA63880

open scoped ArithmeticFunction.sigma

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- A term $n$ is primitive if no proper divisor of $n$ is in the sequence. -/
abbrev IsPrimitiveTerm (n : ℕ) : Prop := {n | A n}.IsPrimitive n

/-- $108$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_108 : A 108 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $540$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_540 : A 540 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $756$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_756 : A 756 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $108$ is a primitive term. -/
@[category test, AMS 11]
theorem isPrimitiveTerm_108 : IsPrimitiveTerm 108 := by
  rw [IsPrimitiveTerm, Set.isPrimitive_iff]
  refine ⟨a_108, ?_⟩
  intro d hd
  have ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  interval_cases d <;> simp_all [A] <;> decide

/-- All members of the sequence satisfy $n \equiv 108 \pmod{216}$. -/
@[category research open, AMS 11]
theorem mod_216_of_a {n : ℕ} (h : A n) : n % 216 = 108 := by
  sorry

/-- The unitary divisors of `m * p`, for a prime `p` not dividing `m > 0`, are the unitary
divisors of `m` and their multiples by `p`. -/
@[category API, AMS 11]
theorem unitaryDivisors_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p) := by
  have hp0 : 0 < p := hp.pos
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := dvd_mul.1 hd
    obtain ⟨t, rfl⟩ := hd₁
    have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
    rcases (Nat.dvd_prime hp).1 hd₂ with h2 | h2 <;> subst d₂
    · -- `d = d₁` is a unitary divisor of `m`
      left
      rw [mul_one] at hcd ⊢
      have e : d₁ * t * p / d₁ = t * p := by
        rw [mul_assoc, Nat.mul_div_cancel_left _ hd₁0]
      rw [e] at hcd
      refine ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_right.1 hcd).1
    · -- `d = d₁ * p`
      right
      have e : d₁ * t * p / (d₁ * p) = t := by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hp0)]
      rw [e] at hcd
      refine ⟨d₁, ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩, rfl⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_left.1 hcd).1
  · rintro (⟨⟨hd, -⟩, hcd⟩ | ⟨d₁, ⟨⟨hd₁, -⟩, hcd⟩, rfl⟩)
    · obtain ⟨t, rfl⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd0] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) p, (Nat.mul_pos hm hp0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd0]
      refine Nat.Coprime.mul_right hcd ?_
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans (dvd_mul_right d t))).symm
    · obtain ⟨t, rfl⟩ := hd₁
      have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd₁0] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right d₁ t) dvd_rfl, (Nat.mul_pos hm hp0).ne'⟩, ?_⟩
      rw [show d₁ * t * p / (d₁ * p) = t by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hp0)]]
      refine Nat.Coprime.mul_left hcd ?_
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans (dvd_mul_left t d₁))

/-- `usigma` is multiplicative at a prime not dividing the argument. -/
@[category API, AMS 11]
theorem usigma_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    usigma (m * p) = usigma m * (p + 1) := by
  have hdisj : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * p)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.1 hd'
    have h1 : d₁ * p ∣ m := (Finset.mem_filter.1 hd).1 |> Nat.mem_divisors.1 |>.1
    exact hpm ((dvd_mul_left p d₁).trans h1)
  unfold usigma
  rw [unitaryDivisors_mul_prime hm hp hpm, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hp.pos h), ← Finset.sum_mul,
    mul_add, mul_one, add_comm]

/-- `σ` is multiplicative at a prime not dividing the argument. -/
@[category API, AMS 11]
theorem sigma_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    σ 1 (m * p) = σ 1 m * (p + 1) := by
  have hσp : σ 1 p = p + 1 := by
    have := ArithmeticFunction.sigma_one_apply_prime_pow hp (i := 1)
    simp [Finset.sum_range_succ] at this
    omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm, hσp]

/-- Membership in the sequence is preserved by multiplying with a prime not dividing the term. -/
@[category API, AMS 11]
theorem A_mul_prime {m p : ℕ} (hA : A m) (hp : p.Prime) (hpm : ¬ p ∣ m) : A (m * p) :=
  ⟨Nat.mul_pos hA.1 hp.pos, by
    rw [sigma_mul_prime hp hpm, usigma_mul_prime hA.1 hp hpm, hA.2]; ring⟩

/-- Conversely, if `m * p` is in the sequence with `p` a prime not dividing `m > 0`, so is `m`. -/
@[category API, AMS 11]
theorem A_of_mul_prime {m p : ℕ} (hm : 0 < m) (hA : A (m * p)) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    A m := by
  refine ⟨hm, ?_⟩
  have h := hA.2
  rw [sigma_mul_prime hp hpm, usigma_mul_prime hm hp hpm, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega) h

/-- Membership in the sequence is preserved by multiplying with a coprime squarefree number. -/
@[category API, AMS 11]
theorem A_mul_of_squarefree (s : ℕ) :
    ∀ m, A m → Squarefree s → m.Coprime s → A (m * s) := by
  induction s using Nat.recOnPrimeCoprime with
  | zero => intro m _ hs; exact absurd hs not_squarefree_zero
  | prime_pow p n hp =>
    intro m hA hs hcop
    have hn : n ≤ 1 := by
      by_contra hn
      exact absurd hs ((Nat.squarefree_pow_iff hp.ne_one (by omega)).not.2 (by omega))
    interval_cases n
    · simpa using hA
    · rw [pow_one] at hcop ⊢
      exact A_mul_prime hA hp ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm)
  | coprime a b _ _ hab iha ihb =>
    intro m hA hs hcop
    rw [← mul_assoc]
    exact ihb (m * a) (iha m hA hs.of_mul_left (Nat.Coprime.coprime_mul_right_right hcop))
      hs.of_mul_right (Nat.Coprime.mul_left (Nat.Coprime.coprime_mul_left_right hcop) hab)

/-- All primitive terms are powerful numbers: if `p` divided `n` exactly once, then `n / p` would
also be in the sequence. -/
@[category textbook, AMS 11]
theorem powerful_of_isPrimitiveTerm {n : ℕ} (h : IsPrimitiveTerm n) : n.Powerful := by
  intro p hp
  by_contra hp2
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn : 0 < n := h.mem.1
  obtain ⟨m, rfl⟩ := hpn
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  have hpm : ¬ p ∣ m := fun hd => hp2 (by rw [sq]; exact Nat.mul_dvd_mul_left p hd)
  have hAm : A m := A_of_mul_prime hm (by rw [mul_comm]; exact h.mem) hpp hpm
  exact h.not_mem_of_dvd_of_lt (dvd_mul_left m p)
    (by have := hpp.two_le; nlinarith) hAm

/-- $108$ is the only primitive term. -/
@[category research open, AMS 11]
theorem unique_primitive_108 {n : ℕ} (h : IsPrimitiveTerm n) : n = 108 := by
  sorry

/-- If $m$ is a primitive term and $s$ is squarefree with $\gcd(m, s) = 1$, then $m \cdot s$
is in the sequence. -/
@[category textbook, AMS 11]
theorem a_of_primitive_mul_squarefree (m s : ℕ) (hm : IsPrimitiveTerm m)
    (hs : Squarefree s) (hcoprime : m.Coprime s) : A (m * s) :=
  A_mul_of_squarefree s m hm.mem hs hcoprime

/-- Non-primitive terms have the form $m \cdot s$ where $m$ is primitive and $s$ is
squarefree with $\gcd(m, s) = 1$. -/
@[category research solved, AMS 11]
theorem exists_primitive_of_a {n : ℕ} (h : A n) :
    ∃ m s, IsPrimitiveTerm m ∧ Squarefree s ∧ m.Coprime s ∧ n = m * s := by
  sorry

end OeisA63880
