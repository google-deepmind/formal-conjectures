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
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.Lattice

@[expose] public section

namespace Nat

/-- The greatest prime divisor of a natural number `n > 1`.

Takes the junk value `0` for `n = 0` and `1` for `n = 1`. -/
def maxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

example : maxPrimeFac 0 = 0 := by decide +kernel
example : maxPrimeFac 1 = 1 := by decide
example : maxPrimeFac 12 = 3 := by decide +kernel
example : maxPrimeFac 97 = 97 := by decide +kernel
example : maxPrimeFac 125 = 5 := by decide +kernel
example : maxPrimeFac 360 = 5 := by decide +kernel

@[simp]
lemma maxPrimeFac_zero :
    maxPrimeFac 0 = 0 := by
  simp [maxPrimeFac, List.getLastI]

@[simp]
lemma maxPrimeFac_one :
    maxPrimeFac 1 = 1 := by
  simp [maxPrimeFac]

lemma prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Prime (maxPrimeFac n) := by
  have hn : n.primeFactorsList ≠ [] := (primeFactorsList_ne_nil n).2 h
  have hmem : n.primeFactorsList.getLast hn ∈ n.primeFactorsList := List.getLast_mem hn
  have hprime : Prime (n.primeFactorsList.getLast hn) := prime_of_mem_primeFactorsList hmem
  simpa [maxPrimeFac, h.ne', List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hn] using hprime

/-- The greatest prime factor of a natural number divides it. -/
lemma maxPrimeFac_dvd {n : ℕ} :
    maxPrimeFac n ∣ n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  case inr.inr =>
    have hlist : n.primeFactorsList ≠ [] := (primeFactorsList_ne_nil n).2 hn
    have hmem : n.primeFactorsList.getLast hlist ∈ n.primeFactorsList :=
      List.getLast_mem hlist
    have hdvd : n.primeFactorsList.getLast hlist ∣ n := dvd_of_mem_primeFactorsList hmem
    simpa [maxPrimeFac, hn.ne', List.getLastI_eq_getLast?_getD,
      List.getLast?_eq_getLast_of_ne_nil hlist] using hdvd
  case inl =>
    simp only [lt_one_iff] at hn
    subst n
    simp
  case inr.inl => simp

/-- Every prime factor of a nonzero natural number is at most its greatest prime factor. -/
lemma le_maxPrimeFac
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have hmem : p ∈ n.primeFactorsList := (mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  have hlist : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have hn_one : n ≠ 1 := ((primeFactorsList_ne_nil n).1 hlist).ne'
  have hp_last : p ≤ n.primeFactorsList.getLast hlist :=
    (primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [maxPrimeFac, hn_one, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hlist] using hp_last

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p := by
  exact le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a prime is the prime itself. -/
@[simp]
lemma Prime.maxPrimeFac_eq_self {p : ℕ} (hp : p.Prime) :
    maxPrimeFac p = p := by
  apply maxPrimeFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos maxPrimeFac_dvd

/-- The greatest prime factor of a nontrivial prime power is its prime base. -/
lemma Prime.maxPrimeFac_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Nat.maxPrimeFac (p ^ k) = p := by
  rw [Nat.maxPrimeFac, hp.primeFactorsList_pow]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hrep : List.replicate (j + 1) p ≠ [] := by
    simp
  simp [hp.ne_one, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hrep]

/-- The greatest prime factor of a natural number is at most that number. -/
lemma maxPrimeFac_le (n : ℕ) :
    maxPrimeFac n ≤ n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  case inr.inr =>
    exact Nat.le_of_dvd (zero_lt_of_lt hn) maxPrimeFac_dvd
  case inl =>
    simp only [lt_one_iff] at hn
    subst n
    simp
  case inr.inl => simp

/-- Away from `n = 1`, the computable greatest prime factor agrees with its supremum
characterization. -/
lemma maxPrimeFac_eq_sSup {n : ℕ} (hn_one : n ≠ 1) :
    maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  case inr.inr =>
    set s := {p : ℕ | p.Prime ∧ p ∣ n}
    have hs₀ : s.Nonempty :=
      ⟨maxPrimeFac n, prime_maxPrimeFac_of_one_lt n hn, maxPrimeFac_dvd⟩
    have hs₁ : BddAbove s := by
      refine ⟨n, ?_⟩
      rintro p ⟨_, hp⟩
      exact Nat.le_of_dvd (zero_lt_of_lt hn) hp
    apply le_antisymm
    · exact le_csSup hs₁
        ⟨prime_maxPrimeFac_of_one_lt n hn, maxPrimeFac_dvd⟩
    · apply csSup_le hs₀
      rintro p ⟨hp, h_dvd⟩
      exact le_maxPrimeFac (zero_lt_of_lt hn).ne' hp h_dvd
  case inl =>
    simp only [lt_one_iff] at hn
    subst n
    simpa using (Set.Infinite.Nat.sSup_eq_zero infinite_setOf_prime).symm
  case inr.inl => exact (hn_one rfl).elim

@[simp]
lemma one_lt_maxPrimeFac_iff (n : ℕ) :
    1 < maxPrimeFac n ↔ 1 < n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn]
  · simp
  · simpa [hn] using (prime_maxPrimeFac_of_one_lt n hn).one_lt

end Nat
